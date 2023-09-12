(* ------------------------------------------------------------------------- *)
(* Helper Theorems - a collection of useful results -- for Functions.        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "helperFunction";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "helperListTheory"; *)
open helperNumTheory helperListTheory;

(* val _ = load "helperSetTheory"; *)
open helperSetTheory;

(* open dependent theories *)
open pred_setTheory prim_recTheory arithmeticTheory;
open listTheory rich_listTheory listRangeTheory;
open dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* Helper Function Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading/syntax:
   (x == y) f          = fequiv x y f
   feq                 = flip (flip o fequiv)
   RISING f            = !x:num. x <= f x
   FALLING f           = !x:num. f x <= x
   SQRT n              = ROOT 2 n
   LOG2 n              = LOG 2 n
   PAIRWISE_COPRIME s  = !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y
   tops b n            = b ** n - 1
   nines n             = tops 10 n
*)
(* Definitions and Theorems (# are exported):

   Function Equivalence as Relation:
   fequiv_def         |- !x y f. fequiv x y f <=> (f x = f y)
   fequiv_refl        |- !f x. (x == x) f
   fequiv_sym         |- !f x y. (x == y) f ==> (y == x) f
   fequiv_trans       |- !f x y z. (x == y) f /\ (y == z) f ==> (x == z) f
   fequiv_equiv_class |- !f. (\x y. (x == y) f) equiv_on univ(:'a)

   Function-based Equivalence:
   feq_class_def       |- !s f n. feq_class f s n = {x | x IN s /\ (f x = n)}
   feq_class_element   |- !f s n x. x IN feq_class f s n <=> x IN s /\ (f x = n)
   feq_class_property  |- !f s x. feq_class f s (f x) = {y | y IN s /\ feq f x y}
   feq_class_fun       |- !f s. feq_class f s o f = (\x. {y | y IN s /\ feq f x y})


   feq_equiv                  |- !s f. feq f equiv_on s
   feq_partition              |- !s f. partition (feq f) s = IMAGE (feq_class f s o f) s
   feq_partition_element      |- !s f t. t IN partition (feq f) s <=>
                                 ?z. z IN s /\ !x. x IN t <=> x IN s /\ (f x = f z)
   feq_partition_element_exists
                              |- !f s x. x IN s <=> ?e. e IN partition (feq f) s /\ x IN e
   feq_partition_element_not_empty
                              |- !f s e. e IN partition (feq f) s ==> e <> {}
   feq_class_eq_preimage      |- !f s. feq_class f s = preimage f s
   feq_partition_by_preimage  |- !f s. partition (feq f) s = IMAGE (preimage f s o f) s
   feq_sum_over_partition     |- !s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)

   finite_card_by_feq_partition   |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)
   finite_card_by_image_preimage  |- !s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)
   finite_card_surj_by_image_preimage
                       |- !f s t. FINITE s /\ SURJ f s t ==>
                                  CARD s = SIGMA CARD (IMAGE (preimage f s) t)
   preimage_image_bij  |- !f s. BIJ (preimage f s) (IMAGE f s) (partition (feq f) s):

   Condition for surjection to be a bijection:
   inj_iff_partition_element_sing
                       |- !f s. INJ f s (IMAGE f s) <=>
                                !e. e IN partition (feq f) s ==> SING e
   inj_iff_partition_element_card_1
                       |- !f s. FINITE s ==>
                                (INJ f s (IMAGE f s) <=>
                                 !e. e IN partition (feq f) s ==> CARD e = 1)
   FINITE_SURJ_IS_INJ  |- !f s t. FINITE s /\
                                  CARD s = CARD t /\ SURJ f s t ==> INJ f s t
   FINITE_SURJ_IS_BIJ  |- !f s t. FINITE s /\
                                  CARD s = CARD t /\ SURJ f s t ==> BIJ f s t

   Function Iteration:
   FUNPOW_2            |- !f x. FUNPOW f 2 x = f (f x)
   FUNPOW_K            |- !n x c. FUNPOW (K c) n x = if n = 0 then x else c
   FUNPOW_MULTIPLE     |- !f k e. 0 < k /\ (FUNPOW f k e = e) ==> !n. FUNPOW f (n * k) e = e
   FUNPOW_MOD          |- !f k e. 0 < k /\ (FUNPOW f k e = e) ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e
   FUNPOW_COMM         |- !f m n x. FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
   FUNPOW_LE_RISING    |- !f m n. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x
   FUNPOW_LE_FALLING   |- !f m n. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x
   FUNPOW_LE_MONO      |- !f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x
   FUNPOW_GE_MONO      |- !f g. (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x
   FUNPOW_SQ           |- !m n. FUNPOW (\n. SQ n) n m = m ** 2 ** n
   FUNPOW_SQ_MOD       |- !m n k. 0 < m /\ 0 < n ==> (FUNPOW (\n. SQ n MOD m) n k = k ** 2 ** n MOD m)
   FUNPOW_ADD1         |- !m n. FUNPOW SUC n m = m + n
   FUNPOW_SUB1         |- !m n. FUNPOW PRE n m = m - n
   FUNPOW_MUL          |- !b m n. FUNPOW ($* b) n m = m * b ** n
   FUNPOW_DIV          |- !b m n. 0 < b ==> FUNPOW (combin$C $DIV b) n m = m DIV b ** n
   FUNPOW_MAX          |- !m n k. 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m)
   FUNPOW_MIN          |- !m n k. 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m)
   FUNPOW_PAIR         |- !f g n x y. FUNPOW (\(x,y). (f x,g y)) n (x,y) = (FUNPOW f n x,FUNPOW g n y)
   FUNPOW_TRIPLE       |- !f g h n x y z. FUNPOW (\(x,y,z). (f x,g y,h z)) n (x,y,z) =
                                          (FUNPOW f n x,FUNPOW g n y,FUNPOW h n z)

   More FUNPOW Theorems:
   LINV_permutes       |- !f s. f PERMUTES s ==> LINV f s PERMUTES s
   FUNPOW_permutes     |- !f s n. f PERMUTES s ==> FUNPOW f n PERMUTES s
   FUNPOW_closure      |- !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s
   FUNPOW_LINV_permutes|- !f s n. f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s
   FUNPOW_LINV_closure |- !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n x IN s
   FUNPOW_LINV_EQ      |- !f s x n. f PERMUTES s /\ x IN s ==>
                                    FUNPOW f n (FUNPOW (LINV f s) n x) = x
   FUNPOW_EQ_LINV      |- !f s x n. f PERMUTES s /\ x IN s ==>
                                    FUNPOW (LINV f s) n (FUNPOW f n x) = x
   FUNPOW_SUB_LINV1    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x)
   FUNPOW_SUB_LINV2    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x)
   FUNPOW_LINV_SUB1    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x)
   FUNPOW_LINV_SUB2    |- !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
                          FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x)
   FUNPOW_LINV_INV     |- !f s x y n. f PERMUTES s /\ x IN s /\ y IN s ==>
                          (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x)

   FUNPOW with incremental cons:
   FUNPOW_cons_head    |- !f n ls. HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls)
   FUNPOW_cons_eq_map_0|- !f u n. FUNPOW (\ls. f (HD ls)::ls) n [u] =
                                  MAP (\j. FUNPOW f j u) (n downto 0)
   FUNPOW_cons_eq_map_1|- !f u n. 0 < n ==>
                                  FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
                                  MAP (\j. FUNPOW f j u) (n downto 1)

   Factorial:
   FACT_0              |- FACT 0 = 1
   FACT_1              |- FACT 1 = 1
   FACT_2              |- FACT 2 = 2
   FACT_EQ_1           |- !n. (FACT n = 1) <=> n <= 1
   FACT_GE_1           |- !n. 1 <= FACT n
   FACT_EQ_SELF        |- !n. (FACT n = n) <=> (n = 1) \/ (n = 2)
   FACT_GE_SELF        |- !n. 0 < n ==> n <= FACT n
   FACT_DIV            |- !n. 0 < n ==> (FACT (n - 1) = FACT n DIV n)
   FACT_EQ_PROD        |- !n. FACT n = PROD_SET (IMAGE SUC (count n))
   FACT_REDUCTION      |- !n m. m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m))
   PRIME_BIG_NOT_DIVIDES_FACT  |- !p k. prime p /\ k < p ==> ~(p divides (FACT k))
   FACT_iff            |- !f. f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n

   Basic GCD, LCM Theorems:
   GCD_COMM            |- !a b. gcd a b = gcd b a
   LCM_SYM             |- !a b. lcm a b = lcm b a
   GCD_0               |- !x. (gcd 0 x = x) /\ (gcd x 0 = x)
   GCD_DIVIDES         |- !m n. 0 < n /\ 0 < m ==> 0 < gcd n m /\ (n MOD gcd n m = 0) /\ (m MOD gcd n m = 0)
   GCD_GCD             |- !m n. gcd n (gcd n m) = gcd n m
   GCD_LCM             |- !m n. gcd m n * lcm m n = m * n
   LCM_DIVISORS        |- !m n. m divides lcm m n /\ n divides lcm m n
   LCM_IS_LCM          |- !m n p. m divides p /\ n divides p ==> lcm m n divides p
   LCM_EQ_0            |- !m n. (lcm m n = 0) <=> (m = 0) \/ (n = 0)
   LCM_REF             |- !a. lcm a a = a
   LCM_DIVIDES         |- !n a b. a divides n /\ b divides n ==> lcm a b divides n
   GCD_POS             |- !m n. 0 < m \/ 0 < n ==> 0 < gcd m n
   LCM_POS             |- !m n. 0 < m /\ 0 < n ==> 0 < lcm m n
   divides_iff_gcd_fix |- !m n. n divides m <=> (gcd n m = n)
   divides_iff_lcm_fix |- !m n. n divides m <=> (lcm n m = m)
   FACTOR_OUT_PRIME    |- !n p. 0 < n /\ prime p /\ p divides n ==>
                          ?m. 0 < m /\ (p ** m) divides n /\ !k. coprime (p ** k) (n DIV p ** m)

   Consequences of Coprime:
   MOD_NONZERO_WHEN_GCD_ONE |- !n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n
   PRODUCT_WITH_GCD_ONE     |- !n x y. coprime n x /\ coprime n y ==> coprime n (x * y)
   MOD_WITH_GCD_ONE         |- !n x. 0 < n /\ coprime n x ==> coprime n (x MOD n)
   GCD_ONE_PROPERTY         |- !n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k
   GCD_MOD_MULT_INV         |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
                                 ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)
   GEN_MULT_INV_DEF         |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
                                     0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\
                                     coprime n (GCD_MOD_MUL_INV n x) /\
                                     ((GCD_MOD_MUL_INV n x * x) MOD n = 1)

   More GCD and LCM Theorems:
   GCD_PROPERTY        |- !a b c. (c = gcd a b) <=> c divides a /\ c divides b /\
                               !x. x divides a /\ x divides b ==> x divides c
   GCD_ASSOC           |- !a b c. gcd a (gcd b c) = gcd (gcd a b) c
   GCD_ASSOC_COMM      |- !a b c. gcd a (gcd b c) = gcd b (gcd a c)
   LCM_PROPERTY        |- !a b c. (c = lcm a b) <=> a divides c /\ b divides c /\
                          !x. a divides x /\ b divides x ==> c divides x
   LCM_ASSOC           |- !a b c. lcm a (lcm b c) = lcm (lcm a b)
   LCM_ASSOC_COMM      |- !a b c. lcm a (lcm b c) = lcm b (lcm a c)
   GCD_SUB_L           |- !a b. b <= a ==> (gcd (a - b) b = gcd a b)
   GCD_SUB_R           |- !a b. a <= b ==> (gcd a (b - a) = gcd a b)
   LCM_EXCHANGE        |- !a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c)
   LCM_COPRIME         |- !m n. coprime m n ==> (lcm m n = m * n)
   LCM_COMMON_FACTOR   |- !m n k. lcm (k * m) (k * n) = k * lcm m n
   LCM_COMMON_COPRIME  |- !a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c
   GCD_MULTIPLE        |- !m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)
   GCD_MULTIPLE_ALT    |- !m n. gcd (m * n) n = n
   GCD_SUB_MULTIPLE    |- !a b k. k * a <= b ==> (gcd a b = gcd a (b - k * a))
   GCD_SUB_MULTIPLE_COMM
                       |- !a b k. k * a <= b ==> (gcd b a = gcd a (b - k * a))
   GCD_MOD             |- !m n. 0 < m ==> (gcd m n = gcd m (n MOD m))
   GCD_MOD_COMM        |- !m n. 0 < m ==> (gcd n m = gcd (n MOD m) m)
   GCD_EUCLID          |- !a b c. gcd a (b * a + c) = gcd a c
   GCD_REDUCE          |- !a b c. gcd (b * a + c) a = gcd a c
   GCD_REDUCE_BY_COPRIME
                       |- !m n k. coprime m k ==> gcd m (k * n) = gcd m n
   gcd_le              |- !m n. 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n
   gcd_divides_iff     |- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c)
   gcd_linear_thm      |- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c)
   gcd_linear_mod_thm  |- !n a b. 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n
   gcd_linear_mod_1    |- !a b. 0 < a ==> ?q. (q * b) MOD a = gcd a b MOD a
   gcd_linear_mod_2    |- !a b. 0 < b ==> ?p. (p * a) MOD b = gcd a b MOD b
   gcd_linear_mod_prod |- !a b. 0 < a /\ 0 < b ==>
                          ?p q. (p * a + q * b) MOD (a * b) = gcd a b MOD (a * b)
   coprime_linear_mod_prod
                       |- !a b. 0 < a /\ 0 < b /\ coprime a b ==>
                          ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b)
   gcd_multiple_linear_mod_thm
                       |- !n a b c. 0 < n /\ 0 < a /\ gcd a b divides c ==>
                              ?p q. (p * a + q * b) MOD n = c MOD n
   gcd_multiple_linear_mod_prod
                       |- !a b c. 0 < a /\ 0 < b /\ gcd a b divides c ==>
                            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
   coprime_multiple_linear_mod_prod
                       |- !a b c. 0 < a /\ 0 < b /\ coprime a b ==>
                            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)

   Coprime Theorems:
   coprime_SUC         |- !n. coprime n (n + 1)
   coprime_PRE         |- !n. 0 < n ==> coprime (n - 1) n
   coprime_0L          |- !n. coprime 0 n <=> (n = 1)
   coprime_0R          |- !n. coprime n 0 <=> (n = 1)
   coprime_0           |- !n. (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1)
   coprime_sym         |- !x y. coprime x y <=> coprime y x
   coprime_neq_1       |- !n k. coprime k n /\ n <> 1 ==> k <> 0
   coprime_gt_1        |- !n k. coprime k n /\ 1 < n ==> 0 < k
   coprime_exp                  |- !c m. coprime c m ==> !n. coprime (c ** n) m
   coprime_exp_comm             |- !a b. coprime a b ==> !n. coprime a (b ** n)
   coprime_iff_coprime_exp      |- !n. 0 < n ==> !a b. coprime a b <=> coprime a (b ** n)
   coprime_product_coprime      |- !x y z. coprime x z /\ coprime y z ==> coprime (x * y) z
   coprime_product_coprime_sym  |- !x y z. coprime z x /\ coprime z y ==> coprime z (x * y)
   coprime_product_coprime_iff  |- !x y z. coprime x z ==> (coprime y z <=> coprime (x * y) z)
   coprime_product_divides      |- !n a b. a divides n /\ b divides n /\ coprime a b ==> a * b divides n
   coprime_mod                  |- !m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)
   coprime_mod_iff              |- !m n. 0 < m ==> (coprime m n <=> coprime m (n MOD m))
   coprime_not_divides          |- !m n. 1 < n /\ coprime n m ==> ~(n divides m)
   coprime_factor_not_divides   |- !n k. 1 < n /\ coprime n k ==>
                                   !p. 1 < p /\ p divides n ==> ~(p divides k)
   coprime_factor_coprime       |- !m n. m divides n ==> !k. coprime n k ==> coprime m k
   coprime_common_factor        |- !a b c. coprime a b /\ c divides a /\ c divides b ==> c = 1
   prime_not_divides_coprime    |- !n p. prime p /\ ~(p divides n) ==> coprime p n
   prime_not_coprime_divides    |- !n p. prime p /\ ~(coprime p n) ==> p divides n
   coprime_prime_factor_coprime |- !n p. 1 < n /\ prime p /\ p divides n ==>
                                   !k. coprime n k ==> coprime p k
   coprime_all_le_imp_lt     |- !n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n
   coprime_condition         |- !m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=>
                                      !j. 1 < j /\ j <= m ==> coprime j n
   coprime_by_le_not_divides |- !m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n
   coprime_by_prime_factor   |- !m n. coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n)
   coprime_by_prime_factor_le|- !m n. 0 < m /\ 0 < n ==>
                                     (coprime m n <=>
                                  !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n))
   coprime_linear_mult       |- !a b p q. coprime a b /\ coprime p b /\ coprime q a ==>
                                          coprime (p * a + q * b) (a * b)
   coprime_linear_mult_iff   |- !a b p q. coprime a b ==>
                                         (coprime p b /\ coprime q a <=> coprime (p * a + q * b) (a * b))
   coprime_prime_power       |- !p n. prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q)
   prime_coprime_all_lt      |- !n. prime n ==> !m. 0 < m /\ m < n ==> coprime n m
   prime_coprime_all_less    |- !m n. prime n /\ m < n ==> !j. 0 < j /\ j <= m ==> coprime n j
   prime_iff_coprime_all_lt  |- !n. prime n <=> 1 < n /\ !j. 0 < j /\ j < n ==> coprime n j
   prime_iff_no_proper_factor|- !n. prime n <=> 1 < n /\ !j. 1 < j /\ j < n ==> ~(j divides n)
   prime_always_bigger       |- !n. ?p. prime p /\ n < p
   divides_imp_coprime_with_successor   |- !m n. n divides m ==> coprime n (SUC m)
   divides_imp_coprime_with_predecessor |- !m n. 0 < m /\ n divides m ==> coprime n (PRE m)
   gcd_coprime_cancel        |- !m n p. coprime p n ==> (gcd (p * m) n = gcd m n)
   primes_coprime            |- !p q. prime p /\ prime q /\ p <> q ==> coprime p q
   every_coprime_prod_set_coprime       |- !s. FINITE s ==>
                                !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s)

   Pairwise Coprime Property:
   pairwise_coprime_insert   |- !s e. e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
                                      (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s
   pairwise_coprime_prod_set_subset_divides
                             |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                                !t. t SUBSET s ==> PROD_SET t divides PROD_SET s
   pairwise_coprime_partition_coprime    |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                             !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v)
   pairwise_coprime_prod_set_partition  |- !s. FINITE s /\ PAIRWISE_COPRIME s ==>
                                           !u v. (s = u UNION v) /\ DISJOINT u v ==>
                             (PROD_SET s = PROD_SET u * PROD_SET v) /\ coprime (PROD_SET u) (PROD_SET v)

   GCD divisibility condition of Power Predecessors:
   power_predecessor_division_eqn  |- !t m n. 0 < t /\ m <= n ==>
                                       tops t n = t ** (n - m) * tops t m + tops t (n - m)
   power_predecessor_division_alt  |- !t m n. 0 < t /\ m <= n ==>
                                       tops t n - t ** (n - m) * tops t m = tops t (n - m)
   power_predecessor_gcd_reduction |- !t n m. m <= n ==>
                                      (gcd (tops t n) (tops t m) = gcd (tops t m) (tops t (n - m)))
   power_predecessor_gcd_identity  |- !t n m. gcd (tops t n) (tops t m) = tops t (gcd n m)
   power_predecessor_divisibility  |- !t n m. 1 < t ==> (tops t n divides tops t m <=> n divides m)
   power_predecessor_divisor       |- !t n. t - 1 divides tops t n

   nines_division_eqn  |- !m n. m <= n ==> nines n = 10 ** (n - m) * nines m + nines (n - m): thm
   nines_division_alt  |- !m n. m <= n ==> nines n - 10 ** (n - m) * nines m = nines (n - m): thm
   nines_gcd_reduction |- !n m. m <= n ==> gcd (nines n) (nines m) = gcd (nines m) (nines (n - m)): thm
   nines_gcd_identity  |- !n m. gcd (nines n) (nines m) = nines (gcd n m): thm
   nines_divisibility  |- !n m. nines n divides nines m <=> n divides m: thm
   nines_divisor       |- !n. 9 divides nines n: thm

   GCD involving Powers:
   prime_divides_prime_power  |- !m n k. prime m /\ prime n /\ m divides n ** k ==> (m = n)
   prime_power_factor         |- !n p. 0 < n /\ prime p ==> ?q m. (n = p ** m * q) /\ coprime p q
   prime_power_divisor        |- !p n a. prime p /\ a divides p ** n ==> ?j. j <= n /\ (a = p ** j)
   prime_powers_eq      |- !p q. prime p /\ prime q ==> !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n)
   prime_powers_coprime |- !p q. prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n)
   prime_powers_divide  |- !p q. prime p /\ prime q ==>
                           !m n. 0 < m ==> (p ** m divides q ** n <=> (p = q) /\ m <= n)
   gcd_powers           |- !b m n. gcd (b ** m) (b ** n) = b ** MIN m n
   lcm_powers           |- !b m n. lcm (b ** m) (b ** n) = b ** MAX m n
   coprime_power_and_power_predecessor   |- !b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1)
   coprime_power_and_power_successor     |- !b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1)

   Useful Theorems:
   PRIME_EXP_FACTOR    |- !p q n. prime p /\ q divides p ** n ==> (q = 1) \/ p divides q
   FACT_MOD_PRIME      |- !p n. prime p /\ n < p ==> FACT n MOD p <> 0:
*)

(* ------------------------------------------------------------------------- *)
(* Function Equivalence as Relation                                          *)
(* ------------------------------------------------------------------------- *)

(* For function f on a domain D, x, y in D are "equal" if f x = f y. *)
Definition fequiv_def:
  fequiv x y f <=> (f x = f y)
End
Overload "==" = ``fequiv``
val _ = set_fixity "==" (Infix(NONASSOC, 450));

(* Theorem: [Reflexive] (x == x) f *)
(* Proof: by definition,
   and f x = f x.
*)
Theorem fequiv_refl[simp]:  !f x. (x == x) f
Proof rw_tac std_ss[fequiv_def]
QED

(* Theorem: [Symmetric] (x == y) f ==> (y == x) f *)
(* Proof: by defintion,
   and f x = f y means the same as f y = f x.
*)
val fequiv_sym = store_thm(
  "fequiv_sym",
  ``!f x y. (x == y) f ==> (y == x) f``,
  rw_tac std_ss[fequiv_def]);

(* no export of commutativity *)

(* Theorem: [Transitive] (x == y) f /\ (y == z) f ==> (x == z) f *)
(* Proof: by defintion,
   and f x = f y
   and f y = f z
   implies f x = f z.
*)
val fequiv_trans = store_thm(
  "fequiv_trans",
  ``!f x y z. (x == y) f /\ (y == z) f ==> (x == z) f``,
  rw_tac std_ss[fequiv_def]);

(* Theorem: fequiv (==) is an equivalence relation on the domain. *)
(* Proof: by reflexive, symmetric and transitive. *)
val fequiv_equiv_class = store_thm(
  "fequiv_equiv_class",
  ``!f. (\x y. (x == y) f) equiv_on univ(:'a)``,
  rw_tac std_ss[equiv_on_def, fequiv_def, EQ_IMP_THM]);

(* ------------------------------------------------------------------------- *)
(* Function-based Equivalence                                                *)
(* ------------------------------------------------------------------------- *)

Overload feq = “flip (flip o fequiv)”
Overload feq_class[inferior] = “preimage”

(* Theorem: x IN feq_class f s n <=> x IN s /\ (f x = n) *)
(* Proof: by feq_class_def *)
Theorem feq_class_element = in_preimage

(* Note:
    y IN equiv_class (feq f) s x
<=> y IN s /\ (feq f x y)      by equiv_class_element
<=> y IN s /\ (f x = f y)      by feq_def
*)

(* Theorem: feq_class f s (f x) = equiv_class (feq f) s x *)
(* Proof:
     feq_class f s (f x)
   = {y | y IN s /\ (f y = f x)}    by feq_class_def
   = {y | y IN s /\ (f x = f y)}
   = {y | y IN s /\ (feq f x y)}    by feq_def
   = equiv_class (feq f) s x        by notation
*)
val feq_class_property = store_thm(
  "feq_class_property",
  ``!f s x. feq_class f s (f x) = equiv_class (feq f) s x``,
  rw[in_preimage, EXTENSION, fequiv_def] >> metis_tac[]);

(* Theorem: (feq_class f s) o f = equiv_class (feq f) s *)
(* Proof: by FUN_EQ_THM, feq_class_property *)
val feq_class_fun = store_thm(
  "feq_class_fun",
  ``!f s. (feq_class f s) o f = equiv_class (feq f) s``,
  rw[FUN_EQ_THM, feq_class_property]);

(* Theorem: feq f equiv_on s *)
(* Proof: by equiv_on_def, feq_def *)
val feq_equiv = store_thm(
  "feq_equiv",
  ``!s f. feq f equiv_on s``,
  rw[equiv_on_def, fequiv_def] >>
  metis_tac[]);

(* Theorem: partition (feq f) s = IMAGE ((feq_class f s) o f) s *)
(* Proof:
   Use partition_def |> ISPEC ``feq f`` |> ISPEC ``(s:'a -> bool)``;

    partition (feq f) s
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ feq f x y})}     by partition_def
  = {t | ?x. x IN s /\ (t = {y | y IN s /\ (f x = f y)})}   by feq_def
  = {t | ?x. x IN s /\ (t = feq_class f s (f x))}           by feq_class_def
  = {feq_class f s (f x) | x | x IN s }                     by rewriting
  = IMAGE (feq_class f s) (IMAGE f s)                       by IN_IMAGE
  = IMAGE ((feq_class f s) o f) s                           by IMAGE_COMPOSE
*)
val feq_partition = store_thm(
  "feq_partition",
  ``!s f. partition (feq f) s = IMAGE ((feq_class f s) o f) s``,
  rw[partition_def, fequiv_def, in_preimage, EXTENSION, EQ_IMP_THM] >>
  metis_tac[]);

(* Theorem: t IN partition (feq f) s <=> ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z)) *)
(* Proof: by feq_partition, feq_class_def, EXTENSION *)
Theorem feq_partition_element:
  !s f t. t IN partition (feq f) s <=>
          ?z. z IN s /\ (!x. x IN t <=> x IN s /\ (f x = f z))
Proof
  rw[feq_partition, in_preimage, EXTENSION] >> metis_tac[]
QED

(* Theorem: x IN s <=> ?e. e IN partition (feq f) s /\ x IN e *)
(* Proof:
   Note (feq f) equiv_on s         by feq_equiv
   This result follows             by partition_element_exists
*)
Theorem feq_partition_element_exists:
  !f s x. x IN s <=> ?e. e IN partition (feq f) s /\ x IN e
Proof
  simp[feq_equiv, partition_element_exists]
QED

(* Theorem: e IN partition (feq f) s ==> e <> {} *)
(* Proof:
   Note (feq f) equiv_on s     by feq_equiv
     so e <> {}                by partition_element_not_empty
*)
Theorem feq_partition_element_not_empty:
  !f s e. e IN partition (feq f) s ==> e <> {}
Proof
  metis_tac[feq_equiv, partition_element_not_empty]
QED

(* Theorem: partition (feq f) s = IMAGE (preimage f s o f) s *)
(* Proof:
       x IN partition (feq f) s
   <=> ?z. z IN s /\ !j. j IN x <=> j IN s /\ (f j = f z)      by feq_partition_element
   <=> ?z. z IN s /\ !j. j IN x <=> j IN (preimage f s (f z))  by preimage_element
   <=> ?z. z IN s /\ (x = preimage f s (f z))                  by EXTENSION
   <=> ?z. z IN s /\ (x = (preimage f s o f) z)                by composition (o_THM)
   <=> x IN IMAGE (preimage f s o f) s                         by IN_IMAGE
   Hence partition (feq f) s = IMAGE (preimage f s o f) s      by EXTENSION

   or,
     partition (feq f) s
   = IMAGE (feq_class f s o f) s     by feq_partition
   = IMAGE (preiamge f s o f) s      by feq_class_eq_preimage
*)
val feq_partition_by_preimage = feq_partition

(* Theorem: FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s) *)
(* Proof:
   Since (feq f) equiv_on s   by feq_equiv
   Hence !g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)  by set_sigma_by_partition
*)
val feq_sum_over_partition = store_thm(
  "feq_sum_over_partition",
  ``!s. FINITE s ==> !f g. SIGMA g s = SIGMA (SIGMA g) (partition (feq f) s)``,
  rw[feq_equiv, set_sigma_by_partition]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s) *)
(* Proof:
   Note feq equiv_on s   by feq_equiv
   The result follows    by partition_CARD
*)
val finite_card_by_feq_partition = store_thm(
  "finite_card_by_feq_partition",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (partition (feq f) s)``,
  rw[feq_equiv, partition_CARD]);

(* Theorem: FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s) *)
(* Proof:
   Note (feq f) equiv_on s                       by feq_equiv
        CARD s
      = SIGMA CARD (partition (feq f) s)         by partition_CARD
      = SIGMA CARD (IMAGE (preimage f s o f) s)  by feq_partition_by_preimage
*)
val finite_card_by_image_preimage = store_thm(
  "finite_card_by_image_preimage",
  ``!s. FINITE s ==> !f. CARD s = SIGMA CARD (IMAGE ((preimage f s) o f) s)``,
  rw[feq_equiv, partition_CARD, GSYM feq_partition]);

(* Theorem: FINITE s /\ SURJ f s t ==>
            CARD s = SIGMA CARD (IMAGE (preimage f s) t) *)
(* Proof:
     CARD s
   = SIGMA CARD (IMAGE (preimage f s o f) s)           by finite_card_by_image_preimage
   = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))     by IMAGE_COMPOSE
   = SIGMA CARD (IMAGE (preimage f s) t)               by IMAGE_SURJ
*)
Theorem finite_card_surj_by_image_preimage:
  !f s t. FINITE s /\ SURJ f s t ==>
          CARD s = SIGMA CARD (IMAGE (preimage f s) t)
Proof
  rpt strip_tac >>
  `CARD s = SIGMA CARD (IMAGE (preimage f s o f) s)` by rw[finite_card_by_image_preimage] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) (IMAGE f s))` by rw[IMAGE_COMPOSE] >>
  `_ = SIGMA CARD (IMAGE (preimage f s) t)` by fs[IMAGE_SURJ] >>
  simp[]
QED

(* Theorem: BIJ (preimage f s) (IMAGE f s) (partition (feq f) s) *)
(* Proof:
   Let g = preimage f s, t = IMAGE f s.
   Note INJ g t (POW s)                        by preimage_image_inj
     so BIJ g t (IMAGE g t)                    by INJ_IMAGE_BIJ
    But IMAGE g t
      = IMAGE (preimage f s) (IMAGE f s)       by notation
      = IMAGE (preimage f s o f) s             by IMAGE_COMPOSE
      = partition (feq f) s                    by feq_partition_by_preimage
   Thus BIJ g t (partition (feq f) s)          by above
*)
Theorem preimage_image_bij:
  !f s. BIJ (preimage f s) (IMAGE f s) (partition (feq f) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `g = preimage f s` >>
  qabbrev_tac `t = IMAGE f s` >>
  `BIJ g t (IMAGE g t)` by metis_tac[preimage_image_inj, INJ_IMAGE_BIJ] >>
  simp[IMAGE_COMPOSE, feq_partition, Abbr`g`, Abbr`t`]
QED

(* ------------------------------------------------------------------------- *)
(* Condition for surjection to be a bijection.                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e *)
(* Proof:
   If part: e IN partition (feq f) s ==> SING e
          e IN partition (feq f) s
      <=> ?z. z IN s /\ !x. x IN e <=> x IN s /\ f x = f z
                                               by feq_partition_element
      Thus z IN e, so e <> {}                  by MEMBER_NOT_EMPTY
       and !x. x IN e ==> x = z                by INJ_DEF
        so SING e                              by SING_ONE_ELEMENT
   Only-if part: !e. e IN partition (feq f) s ==> SING e ==> INJ f s (IMAGE f s)
      By INJ_DEF, IN_IMAGE, this is to show:
         !x y. x IN s /\ y IN s /\ f x = f y ==> x = y
      Note ?e. e IN (partition (feq f) s) /\ x IN e
                                               by feq_partition_element_exists
       and y IN e                              by feq_partition_element
      then SING e                              by implication
        so x = y                               by IN_SING
*)
Theorem inj_iff_partition_element_sing:
  !f s. INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> SING e
Proof
  rw[EQ_IMP_THM] >| [
    fs[feq_partition_element, INJ_DEF] >>
    `e <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
    simp[SING_ONE_ELEMENT],
    rw[INJ_DEF] >>
    `?e. e IN (partition (feq f) s) /\ x IN e` by fs[GSYM feq_partition_element_exists] >>
    `y IN e` by metis_tac[feq_partition_element] >>
    metis_tac[SING_DEF, IN_SING]
  ]
QED

(* Theorem: FINITE s ==>
            (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1) *)
(* Proof:
       INJ f s (IMAGE f s)
   <=> !e. e IN (partition (feq f) s) ==> SING e       by inj_iff_partition_element_sing
   <=> !e. e IN (partition (feq f) s) ==> CARD e = 1   by FINITE_partition, CARD_EQ_1
*)
Theorem inj_iff_partition_element_card_1:
  !f s. FINITE s ==>
        (INJ f s (IMAGE f s) <=> !e. e IN (partition (feq f) s) ==> CARD e = 1)
Proof
  metis_tac[inj_iff_partition_element_sing, FINITE_partition, CARD_EQ_1]
QED

(* Idea: for a finite domain, with target same size, surjection means injection. *)

(* Theorem: FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t *)
(* Proof:
   Let p = partition (feq f) s.
   Note IMAGE f s = t              by IMAGE_SURJ
     so FINITE t                   by IMAGE_FINITE
    and CARD s = SIGMA CARD p      by finite_card_by_feq_partition
    and CARD t = CARD p            by preimage_image_bij, bij_eq_card
   Thus CARD p = SIGMA CARD p      by given CARD s = CARD t
    Now FINITE p                   by FINITE_partition
    and !e. e IN p ==> FINITE e    by FINITE_partition
    and !e. e IN p ==> e <> {}     by feq_partition_element_not_empty
     so !e. e IN p ==> CARD e <> 0 by CARD_EQ_0
   Thus !e. e IN p ==> CARD e = 1  by card_eq_sigma_card
     or INJ f s (IMAGE f s)        by inj_iff_partition_element_card_1
     so INJ f s t                  by IMAGE f s = t
*)
Theorem FINITE_SURJ_IS_INJ:
  !f s t. FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> INJ f s t
Proof
  rpt strip_tac >>
  imp_res_tac finite_card_by_feq_partition >>
  first_x_assum (qspec_then `f` strip_assume_tac) >>
  qabbrev_tac `p = partition (feq f) s` >>
  `IMAGE f s = t` by fs[IMAGE_SURJ] >>
  `FINITE t` by rw[] >>
  `CARD t = CARD p` by metis_tac[preimage_image_bij, FINITE_BIJ_CARD] >>
  `FINITE p /\ !e. e IN p ==> FINITE e` by metis_tac[FINITE_partition] >>
  `!e. e IN p ==> CARD e <> 0` by metis_tac[feq_partition_element_not_empty, CARD_EQ_0] >>
  `!e. e IN p ==> CARD e = 1` by metis_tac[card_eq_sigma_card] >>
  metis_tac[inj_iff_partition_element_card_1]
QED

(* Finally! show that SURJ can imply BIJ. *)

(* Theorem: FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> BIJ f s t *)
(* Proof:
   Note INJ f s t              by FINITE_SURJ_IS_INJ
     so BIJ f s t              by BIJ_DEF, SURJ f s t
*)
Theorem FINITE_SURJ_IS_BIJ:
  !f s t. FINITE s /\ CARD s = CARD t /\ SURJ f s t ==> BIJ f s t
Proof
  simp[FINITE_SURJ_IS_INJ, BIJ_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Function Iteration                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FUNPOW f 2 x = f (f x) *)
(* Proof: by definition. *)
val FUNPOW_2 = store_thm(
  "FUNPOW_2",
  ``!f x. FUNPOW f 2 x = f (f x)``,
  simp_tac bool_ss [FUNPOW, TWO, ONE]);

(* Theorem: FUNPOW (K c) n x = if n = 0 then x else c *)
(* Proof:
   By induction on n.
   Base: !x c. FUNPOW (K c) 0 x = if 0 = 0 then x else c
           FUNPOW (K c) 0 x
         = x                         by FUNPOW
         = if 0 = 0 then x else c    by 0 = 0 is true
   Step: !x c. FUNPOW (K c) n x = if n = 0 then x else c ==>
         !x c. FUNPOW (K c) (SUC n) x = if SUC n = 0 then x else c
           FUNPOW (K c) (SUC n) x
         = FUNPOW (K c) n ((K c) x)         by FUNPOW
         = if n = 0 then ((K c) c) else c   by induction hypothesis
         = if n = 0 then c else c           by K_THM
         = c                                by either case
         = if SUC n = 0 then x else c       by SUC n = 0 is false
*)
val FUNPOW_K = store_thm(
  "FUNPOW_K",
  ``!n x c. FUNPOW (K c) n x = if n = 0 then x else c``,
  Induct >-
  rw[] >>
  metis_tac[FUNPOW, combinTheory.K_THM, SUC_NOT_ZERO]);

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f (n*k) e = e *)
(* Proof:
   By induction on n:
   Base case: FUNPOW f (0 * k) e = e
     FUNPOW f (0 * k) e
   = FUNPOW f 0 e          by arithmetic
   = e                     by FUNPOW_0
   Step case: FUNPOW f (n * k) e = e ==> FUNPOW f (SUC n * k) e = e
     FUNPOW f (SUC n * k) e
   = FUNPOW f (k + n * k) e         by arithmetic
   = FUNPOW f k (FUNPOW (n * k) e)  by FUNPOW_ADD.
   = FUNPOW f k e                   by induction hypothesis
   = e                              by given
*)
val FUNPOW_MULTIPLE = store_thm(
  "FUNPOW_MULTIPLE",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f (n*k) e = e``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[MULT_COMM, MULT_SUC, FUNPOW_ADD]);

(* Theorem: 0 < k /\ FUNPOW f k e = e  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e *)
(* Proof:
     FUNPOW f n e
   = FUNPOW f ((n DIV k) * k + (n MOD k)) e       by division algorithm
   = FUNPOW f ((n MOD k) + (n DIV k) * k) e       by arithmetic
   = FUNPOW f (n MOD k) (FUNPOW (n DIV k) * k e)  by FUNPOW_ADD
   = FUNPOW f (n MOD k) e                         by FUNPOW_MULTIPLE
*)
val FUNPOW_MOD = store_thm(
  "FUNPOW_MOD",
  ``!f k e. 0 < k /\ (FUNPOW f k e = e)  ==> !n. FUNPOW f n e = FUNPOW f (n MOD k) e``,
  rpt strip_tac >>
  `n = (n MOD k) + (n DIV k) * k` by metis_tac[DIVISION, ADD_COMM] >>
  metis_tac[FUNPOW_ADD, FUNPOW_MULTIPLE]);

(* Theorem: FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x) *)
(* Proof: by FUNPOW_ADD, ADD_COMM *)
Theorem FUNPOW_COMM:
  !f m n x. FUNPOW f m (FUNPOW f n x) = FUNPOW f n (FUNPOW f m x)
Proof
  metis_tac[FUNPOW_ADD, ADD_COMM]
QED

(* Overload a RISING function *)
val _ = overload_on ("RISING", ``\f. !x:num. x <= f x``);

(* Overload a FALLING function *)
val _ = overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* Theorem: RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f m x <= FUNPOW f 0 x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x ==>
          !m. m <= SUC n ==> FUNPOW f m x <= FUNPOW f (SUC n) x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
             FUNPOW f m x
          <= FUNPOW f n x            by induction hypothesis
          <= f (FUNPOW f n x)        by RISING f
           = FUNPOW f (SUC n) x      by FUNPOW_SUC
*)
val FUNPOW_LE_RISING = store_thm(
  "FUNPOW_LE_RISING",
  ``!f m n. RISING f /\ m <= n ==> !x. FUNPOW f m x <= FUNPOW f n x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f m x <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= f (FUNPOW f n x)` by rw[] >>
    `f (FUNPOW f n x) = FUNPOW f (SUC n) x` by rw[FUNPOW_SUC] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x *)
(* Proof:
   By induction on n.
   Base: !m. m <= 0 ==> !x. FUNPOW f 0 x <= FUNPOW f m x
      Note m = 0, and FUNPOW f 0 x <= FUNPOW f 0 x.
   Step:  !m. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x ==>
          !m. m <= SUC n ==> FUNPOW f (SUC n) x <= FUNPOW f m x
      Note m <= n or m = SUC n.
      If m = SUC n, this is trivial.
      If m <= n,
            FUNPOW f (SUC n) x
          = f (FUNPOW f n x)         by FUNPOW_SUC
         <= FUNPOW f n x             by FALLING f
         <= FUNPOW f m x             by induction hypothesis
*)
val FUNPOW_LE_FALLING = store_thm(
  "FUNPOW_LE_FALLING",
  ``!f m n. FALLING f /\ m <= n ==> !x. FUNPOW f n x <= FUNPOW f m x``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rpt strip_tac >>
  `(m <= n) \/ (m = SUC n)` by decide_tac >| [
    `FUNPOW f (SUC n) x = f (FUNPOW f n x)` by rw[FUNPOW_SUC] >>
    `f (FUNPOW f n x) <= FUNPOW f n x` by rw[] >>
    `FUNPOW f n x <= FUNPOW f m x` by rw[] >>
    decide_tac,
    rw[]
  ]);

(* Theorem: (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= g (FUNPOW f n x)      by !x. f x <= g x
      <= g (FUNPOW g n x)      by induction hypothesis, MONO g
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_LE_MONO = store_thm(
  "FUNPOW_LE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= g (FUNPOW f n x)` by rw[] >>
  `g (FUNPOW f n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note:
There is no FUNPOW_LE_RMONO. FUNPOW_LE_MONO says:
|- !f g. (!x. f x <= g x) /\ MONO g ==> !n x. FUNPOW f n x <= FUNPOW g n x
To compare the terms in these two sequences:
     x, f x, f (f x), f (f (f x)), ......
     x, g x, g (g x), g (g (g x)), ......
For the first pair:       x <= x.
For the second pair:    f x <= g x,      as g is cover.
For the third pair: f (f x) <= g (f x)   by g is cover,
                            <= g (g x)   by MONO g, and will not work if RMONO g.
*)

(* Theorem: (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x <= FUNPOW g 0 x
         FUNPOW f 0 x          by FUNPOW_0
       = x
       <= x = FUNPOW g 0 x     by FUNPOW_0
   Step: FUNPOW f n x <= FUNPOW g n x ==> FUNPOW f (SUC n) x <= FUNPOW g (SUC n) x
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)      by FUNPOW_SUC
      <= f (FUNPOW g n x)      by induction hypothesis, MONO f
      <= g (FUNPOW g n x)      by !x. f x <= g x
       = FUNPOW g (SUC n) x    by FUNPOW_SUC
*)
val FUNPOW_GE_MONO = store_thm(
  "FUNPOW_GE_MONO",
  ``!f g. (!x. f x <= g x) /\ MONO f ==> !n x. FUNPOW f n x <= FUNPOW g n x``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `f (FUNPOW f n x) <= f (FUNPOW g n x)` by rw[] >>
  `f (FUNPOW g n x) <= g (FUNPOW g n x)` by rw[] >>
  decide_tac);

(* Note: the name FUNPOW_SUC is taken:
FUNPOW_SUC  |- !f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)
*)

(* Theorem: FUNPOW SUC n m = m + n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW SUC 0 m = m + 0
      LHS = FUNPOW SUC 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW SUC n m = m + n ==>
         !m. FUNPOW SUC (SUC n) m = m + SUC n
       FUNPOW SUC (SUC n) m
     = FUNPOW SUC n (SUC m)    by FUNPOW
     = (SUC m) + n             by induction hypothesis
     = m + SUC n               by arithmetic
*)
val FUNPOW_ADD1 = store_thm(
  "FUNPOW_ADD1",
  ``!m n. FUNPOW SUC n m = m + n``,
  Induct_on `n` >>
  rw[FUNPOW]);

(* Theorem: FUNPOW PRE n m = m - n *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW PRE 0 m = m - 0
      LHS = FUNPOW PRE 0 m
          = m                  by FUNPOW_0
          = m + 0 = RHS        by ADD_0
   Step: !m. FUNPOW PRE n m = m - n ==>
         !m. FUNPOW PRE (SUC n) m = m - SUC n
       FUNPOW PRE (SUC n) m
     = FUNPOW PRE n (PRE m)    by FUNPOW
     = (PRE m) - n             by induction hypothesis
     = m - PRE n               by arithmetic
*)
val FUNPOW_SUB1 = store_thm(
  "FUNPOW_SUB1",
  ``!m n. FUNPOW PRE n m = m - n``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW]);

(* Theorem: FUNPOW ($* b) n m = m * b ** n *)
(* Proof:
   By induction on n.
   Base: !m. !m. FUNPOW ($* b) 0 m = m * b ** 0
      LHS = FUNPOW ($* b) 0 m
          = m                  by FUNPOW_0
          = m * 1              by MULT_RIGHT_1
          = m * b ** 0 = RHS   by EXP_0
   Step: !m. FUNPOW ($* b) n m = m * b ** n ==>
         !m. FUNPOW ($* b) (SUC n) m = m * b ** SUC n
       FUNPOW ($* b) (SUC n) m
     = FUNPOW ($* b) n (b * m)    by FUNPOW
     = b * m * b ** n             by induction hypothesis
     = m * (b * b ** n)           by arithmetic
     = m * b ** SUC n             by EXP
*)
val FUNPOW_MUL = store_thm(
  "FUNPOW_MUL",
  ``!b m n. FUNPOW ($* b) n m = m * b ** n``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW, EXP]);

(* Theorem: 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n)) *)
(* Proof:
   By induction on n.
   Let f = combin$C $DIV b.
   Base: !m. FUNPOW f 0 m = m DIV b ** 0
      LHS = FUNPOW f 0 m
          = m                     by FUNPOW_0
          = m DIV 1               by DIV_1
          = m DIV (b ** 0) = RHS  by EXP_0
   Step: !m. FUNPOW f n m = m DIV b ** n ==>
         !m. FUNPOW f (SUC n) m = m DIV b ** SUC n
       FUNPOW f (SUC n) m
     = FUNPOW f n (f m)           by FUNPOW
     = FUNPOW f n (m DIV b)       by C_THM
     = (m DIV b) DIV (b ** n)     by induction hypothesis
     = m DIV (b * b ** n)         by DIV_DIV_DIV_MULT, 0 < b, 0 < b ** n
     = m DIV b ** SUC n           by EXP
*)
val FUNPOW_DIV = store_thm(
  "FUNPOW_DIV",
  ``!b m n. 0 < b ==> (FUNPOW (combin$C $DIV b) n m = m DIV (b ** n))``,
  strip_tac >>
  qabbrev_tac `f = combin$C $DIV b` >>
  Induct_on `n` >-
  rw[EXP_0] >>
  rpt strip_tac >>
  `FUNPOW f (SUC n) m = FUNPOW f n (m DIV b)` by rw[FUNPOW, Abbr`f`] >>
  `_ = (m DIV b) DIV (b ** n)` by rw[] >>
  `_ = m DIV (b * b ** n)` by rw[DIV_DIV_DIV_MULT] >>
  `_ = m DIV b ** SUC n` by rw[EXP] >>
  decide_tac);

(* Theorem: FUNPOW SQ n m = m ** (2 ** n) *)
(* Proof:
   By induction on n.
   Base: !m. FUNPOW (\n. SQ n) 0 m = m ** 2 ** 0
        FUNPOW SQ 0 m
      = m               by FUNPOW_0
      = m ** 1          by EXP_1
      = m ** 2 ** 0     by EXP_0
   Step: !m. FUNPOW (\n. SQ n) n m = m ** 2 ** n ==>
         !m. FUNPOW (\n. SQ n) (SUC n) m = m ** 2 ** SUC n
        FUNPOW (\n. SQ n) (SUC n) m
      = SQ (FUNPOW (\n. SQ n) n m)    by FUNPOW_SUC
      = SQ (m ** 2 ** n)              by induction hypothesis
      = (m ** 2 ** n) ** 2            by EXP_2
      = m ** (2 * 2 ** n)             by EXP_EXP_MULT
      = m ** 2 ** SUC n               by EXP
*)
val FUNPOW_SQ = store_thm(
  "FUNPOW_SQ",
  ``!m n. FUNPOW SQ n m = m ** (2 ** n)``,
  Induct_on `n` >-
  rw[] >>
  rw[FUNPOW_SUC, GSYM EXP_EXP_MULT, EXP]);

(* Theorem: 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m) *)
(* Proof:
   Lef f = (\n. SQ n MOD m).
   By induction on n.
   Base: !k. 0 < m /\ 0 < 0 ==> FUNPOW f 0 k = k ** 2 ** 0 MOD m
      True since 0 < 0 = F.
   Step: !k. 0 < m /\ 0 < n ==> FUNPOW f n k = k ** 2 ** n MOD m ==>
         !k. 0 < m /\ 0 < SUC n ==> FUNPOW f (SUC n) k = k ** 2 ** SUC n MOD m
     If n = 1,
       FUNPOW f (SUC 0) k
     = FUNPOW f 1 k             by ONE
     = f k                      by FUNPOW_1
     = SQ k MOD m               by notation
     = (k ** 2) MOD m           by EXP_2
     = (k ** (2 ** 1)) MOD m    by EXP_1
     If n <> 0,
       FUNPOW f (SUC n) k
     = f (FUNPOW f n k)         by FUNPOW_SUC
     = f (k ** 2 ** n MOD m)    by induction hypothesis
     = (k ** 2 ** n MOD m) * (k ** 2 ** n MOD m) MOD m     by notation
     = (k ** 2 ** n * k ** 2 ** n) MOD m                   by MOD_TIMES2
     = (k ** (2 ** n + 2 ** n)) MOD m          by EXP_BASE_MULT
     = (k ** (2 * 2 ** n)) MOD m               by arithmetic
     = (k ** 2 ** SUC n) MOD m                 by EXP
*)
val FUNPOW_SQ_MOD = store_thm(
  "FUNPOW_SQ_MOD",
  ``!m n k. 0 < m /\ 0 < n ==> (FUNPOW (\n. (n * n) MOD m) n k = (k ** 2 ** n) MOD m)``,
  strip_tac >>
  qabbrev_tac `f = \n. SQ n MOD m` >>
  Induct >>
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[Abbr`f`] >>
  rw[FUNPOW_SUC, Abbr`f`] >>
  `(k ** 2 ** n) ** 2 = k ** (2 * 2 ** n)` by rw[GSYM EXP_EXP_MULT] >>
  `_ = k ** 2 ** SUC n` by rw[EXP] >>
  rw[]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MAX x m) 0 k = MAX k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MAX x m) n k = MAX k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MAX x m) (SUC n) k = MAX k m
      If n = 0,
           FUNPOW (\x. MAX x m) (SUC 0) k
         = FUNPOW (\x. MAX x m) 1 k          by ONE
         = (\x. MAX x m) k                   by FUNPOW_1
         = MAX k m                           by function application
      If n <> 0,
           FUNPOW (\x. MAX x m) (SUC n) k
         = f (FUNPOW (\x. MAX x m) n k)      by FUNPOW_SUC
         = (\x. MAX x m) (MAX k m)           by induction hypothesis
         = MAX (MAX k m) m                   by function application
         = MAX k m                           by MAX_IS_MAX, m <= MAX k m
*)
val FUNPOW_MAX = store_thm(
  "FUNPOW_MAX",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MAX x m) n k = MAX k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `m <= MAX k m` by rw[] >>
  rw[MAX_DEF]);

(* Theorem: 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m) *)
(* Proof:
   By induction on n.
   Base: !m k. 0 < 0 ==> FUNPOW (\x. MIN x m) 0 k = MIN k m
      True by 0 < 0 = F.
   Step: !m k. 0 < n ==> FUNPOW (\x. MIN x m) n k = MIN k m ==>
         !m k. 0 < SUC n ==> FUNPOW (\x. MIN x m) (SUC n) k = MIN k m
      If n = 0,
           FUNPOW (\x. MIN x m) (SUC 0) k
         = FUNPOW (\x. MIN x m) 1 k          by ONE
         = (\x. MIN x m) k                   by FUNPOW_1
         = MIN k m                           by function application
      If n <> 0,
           FUNPOW (\x. MIN x m) (SUC n) k
         = f (FUNPOW (\x. MIN x m) n k)      by FUNPOW_SUC
         = (\x. MIN x m) (MIN k m)           by induction hypothesis
         = MIN (MIN k m) m                   by function application
         = MIN k m                           by MIN_IS_MIN, MIN k m <= m
*)
val FUNPOW_MIN = store_thm(
  "FUNPOW_MIN",
  ``!m n k. 0 < n ==> (FUNPOW (\x. MIN x m) n k = MIN k m)``,
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  rw[FUNPOW_SUC] >>
  `MIN k m <= m` by rw[] >>
  rw[MIN_DEF]);

(* Theorem: FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y). (f x,g y)) 0 (x,y) = (FUNPOW f 0 x,FUNPOW g 0 y)
          FUNPOW (\(x,y). (f x,g y)) 0 (x,y)
        = (x,y)                           by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y)    by FUNPOW_0
   Step: FUNPOW (\(x,y). (f x,g y)) n (x,y) = (FUNPOW f n x,FUNPOW g n y) ==>
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y) = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)
         FUNPOW (\(x,y). (f x,g y)) (SUC n) (x,y)
       = (\(x,y). (f x,g y)) (FUNPOW (\(x,y). (f x,g y)) n (x,y)) by FUNPOW_SUC
       = (\(x,y). (f x,g y)) (FUNPOW f n x,FUNPOW g n y)          by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y))                      by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y)                  by FUNPOW_SUC
*)
val FUNPOW_PAIR = store_thm(
  "FUNPOW_PAIR",
  ``!f g n x y. FUNPOW (\(x,y). (f x, g y)) n (x,y) = (FUNPOW f n x, FUNPOW g n y)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);

(* Theorem: FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) = (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z) *)
(* Proof:
   By induction on n.
   Base: FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z) = (FUNPOW f 0 x,FUNPOW g 0 y,FUNPOW h 0 z)
          FUNPOW (\(x,y,z). (f x,g y,h z)) 0 (x,y,z)
        = (x,y)                                         by FUNPOW_0
        = (FUNPOW f 0 x, FUNPOW g 0 y, FUNPOW h 0 z)    by FUNPOW_0
   Step: FUNPOW (\(x,y,z). (f x,g y,h z)) n (x,y,z) =
                (FUNPOW f n x,FUNPOW g n y,FUNPOW h n z) ==>
         FUNPOW (\(x,y,z). (f x,g y,h z)) (SUC n) (x,y,z) =
                (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y,FUNPOW h (SUC n) z)
       Let fun = (\(x,y,z). (f x,g y,h z)).
         FUNPOW fun (SUC n) (x,y, z)
       = fun (FUNPOW fun n (x,y,z))                                   by FUNPOW_SUC
       = fun (FUNPOW f n x,FUNPOW g n y, FUNPOW h n z)                by induction hypothesis
       = (f (FUNPOW f n x),g (FUNPOW g n y), h (FUNPOW h n z))        by function application
       = (FUNPOW f (SUC n) x,FUNPOW g (SUC n) y, FUNPOW h (SUC n) z)  by FUNPOW_SUC
*)
val FUNPOW_TRIPLE = store_thm(
  "FUNPOW_TRIPLE",
  ``!f g h n x y z. FUNPOW (\(x,y,z). (f x, g y, h z)) n (x,y,z) =
                  (FUNPOW f n x, FUNPOW g n y, FUNPOW h n z)``,
  rpt strip_tac >>
  Induct_on `n` >>
  rw[FUNPOW_SUC]);

(* ------------------------------------------------------------------------- *)
(* More FUNPOW Theorems                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f PERMUTES s ==> (LINV f s) PERMUTES s *)
(* Proof: by BIJ_LINV_BIJ *)
Theorem LINV_permutes:
  !f s. f PERMUTES s ==> (LINV f s) PERMUTES s
Proof
  rw[BIJ_LINV_BIJ]
QED

(* Theorem: f PERMUTES s ==> (FUNPOW f n) PERMUTES s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 PERMUTES s
      Note FUNPOW f 0 = I         by FUN_EQ_THM, FUNPOW_0
       and I PERMUTES s           by BIJ_I_SAME
      thus true.
   Step: f PERMUTES s /\ FUNPOW f n PERMUTES s ==>
         FUNPOW f (SUC n) PERMUTES s
      Note FUNPOW f (SUC n)
         = f o (FUNPOW f n)       by FUN_EQ_THM, FUNPOW_SUC
      Thus true                   by BIJ_COMPOSE
*)
Theorem FUNPOW_permutes:
  !f s n. f PERMUTES s ==> (FUNPOW f n) PERMUTES s
Proof
  rpt strip_tac >>
  Induct_on `n` >| [
    `FUNPOW f 0 = I` by rw[FUN_EQ_THM] >>
    simp[BIJ_I_SAME],
    `FUNPOW f (SUC n) = f o (FUNPOW f n)` by rw[FUN_EQ_THM, FUNPOW_SUC] >>
    metis_tac[BIJ_COMPOSE]
  ]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 x IN s
         Since FUNPOW f 0 x = x      by FUNPOW_0
         This is trivially true.
   Step: FUNPOW f n x IN s ==> FUNPOW f (SUC n) x IN s
           FUNPOW f (SUC n) x
         = f (FUNPOW f n x)          by FUNPOW_SUC
         But FUNPOW f n x IN s       by induction hypothesis
          so f (FUNPOW f n x) IN s   by BIJ_ELEMENT, f PERMUTES s
*)
Theorem FUNPOW_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  metis_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* Theorem: f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s *)
(* Proof: by LINV_permutes, FUNPOW_permutes *)
Theorem FUNPOW_LINV_permutes:
  !f s n. f PERMUTES s ==> FUNPOW (LINV f s) n PERMUTES s
Proof
  simp[LINV_permutes, FUNPOW_permutes]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n x IN s *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 x IN s
         Since FUNPOW (LINV f s) 0 x = x   by FUNPOW_0
         This is trivially true.
   Step: FUNPOW (LINV f s) n x IN s ==> FUNPOW (LINV f s) (SUC n) x IN s
           FUNPOW (LINV f s) (SUC n) x
         = (LINV f s) (FUNPOW (LINV f s) n x)   by FUNPOW_SUC
         But FUNPOW (LINV f s) n x IN s         by induction hypothesis
         and (LINV f s) PERMUTES s              by LINV_permutes
          so (LINV f s) (FUNPOW (LINV f s) n x) IN s
                                                by BIJ_ELEMENT
*)
Theorem FUNPOW_LINV_closure:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n x IN s
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `(LINV f s) PERMUTES s` by rw[LINV_permutes] >>
  prove_tac[FUNPOW_SUC, BIJ_ELEMENT]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW f 0 (FUNPOW (LINV f s) 0 x) = x
           FUNPOW f 0 (FUNPOW (LINV f s) 0 x)
         = FUNPOW f 0 x              by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW f n (FUNPOW (LINV f s) n x) = x ==>
         FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x) = x
         Note (FUNPOW (LINV f s) n x) IN s        by FUNPOW_LINV_closure
           FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
         = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))  by FUNPOW_SUC
         = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))    by FUNPOW
         = FUNPOW f n (FUNPOW (LINV f s) n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_LINV_EQ:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW f n (FUNPOW (LINV f s) n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW f (SUC n) (FUNPOW (LINV f s) (SUC n) x)
    = FUNPOW f (SUC n) ((LINV f s) (FUNPOW (LINV f s) n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW f n (f ((LINV f s) (FUNPOW (LINV f s) n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW f n (FUNPOW (LINV f s) n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW (LINV f s) 0 (FUNPOW f 0 x) = x
           FUNPOW (LINV f s) 0 (FUNPOW f 0 x)
         = FUNPOW (LINV f s) 0 x     by FUNPOW_0
         = x                         by FUNPOW_0
   Step: FUNPOW (LINV f s) n (FUNPOW f n x) = x ==>
         FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x) = x
         Note (FUNPOW f n x) IN s                 by FUNPOW_closure
           FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
         = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))           by FUNPOW_SUC
         = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))    by FUNPOW
         = FUNPOW (LINV f s) n (FUNPOW f n x)                     by BIJ_LINV_THM
         = x                                      by induction hypothesis
*)
Theorem FUNPOW_EQ_LINV:
  !f s x n. f PERMUTES s /\ x IN s ==> FUNPOW (LINV f s) n (FUNPOW f n x) = x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `FUNPOW (LINV f s) (SUC n) (FUNPOW f (SUC n) x)
    = FUNPOW (LINV f s) (SUC n) (f (FUNPOW f n x))` by rw[FUNPOW_SUC] >>
  `_ = FUNPOW (LINV f s) n ((LINV f s) (f (FUNPOW f n x)))` by rw[FUNPOW] >>
  `_ = FUNPOW (LINV f s) n (FUNPOW f n x)` by metis_tac[BIJ_LINV_THM, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x) *)
(* Proof:
     FUNPOW f n (FUNPOW (LINV f s) m x)
   = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)   by SUB_ADD, m <= n
   = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                             by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_SUB_LINV1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW f n (FUNPOW (LINV f s) m x)
Proof
  rpt strip_tac >>
  `FUNPOW f n (FUNPOW (LINV f s) m x)
  = FUNPOW f (n - m + m) (FUNPOW (LINV f s) m x)` by simp[] >>
  `_ = FUNPOW f (n - m) (FUNPOW f m (FUNPOW (LINV f s) m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_LINV_EQ] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x) *)
(* Proof:
   Note FUNPOW f (n - m) x IN s                      by FUNPOW_closure
     FUNPOW (LINV f s) m (FUNPOW f n x)
   = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)  by ADD_COMM
   = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))  by FUNPOW_ADD
   = FUNPOW f (n - m) x                              by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_SUB_LINV2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW f (n - m) x = FUNPOW (LINV f s) m (FUNPOW f n x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) m (FUNPOW f n x)
  = FUNPOW (LINV f s) m (FUNPOW f (n - m + m) x)` by simp[] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW (LINV f s) m (FUNPOW f m (FUNPOW f (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW f (n - m) x` by rw[FUNPOW_EQ_LINV, FUNPOW_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x) *)
(* Proof:
     FUNPOW (LINV f s) n (FUNPOW f m x)
   = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)    by SUB_ADD, m <= n
   = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_EQ_LINV
*)
Theorem FUNPOW_LINV_SUB1:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW (LINV f s) n (FUNPOW f m x)
Proof
  rpt strip_tac >>
  `FUNPOW (LINV f s) n (FUNPOW f m x)
  = FUNPOW (LINV f s) (n - m + m) (FUNPOW f m x)` by simp[] >>
  `_ = FUNPOW (LINV f s) (n - m) (FUNPOW (LINV f s) m (FUNPOW f m x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_EQ_LINV] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ m <= n ==>
            FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x) *)
(* Proof:
   Note FUNPOW (LINV f s) (n - m) x IN s             by FUNPOW_LINV_closure
     FUNPOW f m (FUNPOW (LINV f s) n x)
   = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)    by SUB_ADD, m <= n
   = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)  by ADD_COMM
   = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))  by FUNPOW_ADD
   = FUNPOW (LINV f s) (n - m) x                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_SUB2:
  !f s x m n. f PERMUTES s /\ x IN s /\ m <= n ==>
              FUNPOW (LINV f s) (n - m) x = FUNPOW f m (FUNPOW (LINV f s) n x)
Proof
  rpt strip_tac >>
  `FUNPOW f m (FUNPOW (LINV f s) n x)
  = FUNPOW f m (FUNPOW (LINV f s) (n - m + m) x)` by simp[] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) (m + (n - m)) x)` by metis_tac[ADD_COMM] >>
  `_ = FUNPOW f m (FUNPOW (LINV f s) m (FUNPOW (LINV f s) (n - m) x))` by rw[FUNPOW_ADD] >>
  `_ = FUNPOW (LINV f s) (n - m) x` by rw[FUNPOW_LINV_EQ, FUNPOW_LINV_closure] >>
  simp[]
QED

(* Theorem: f PERMUTES s /\ x IN s /\ y IN s ==>
            (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x) *)
(* Proof:
   If part: x = FUNPOW f n y ==> y = FUNPOW (LINV f s) n x)
        FUNPOW (LINV f s) n x)
      = FUNPOW (LINV f s) n (FUNPOW f n y))   by x = FUNPOW f n y
      = y                                     by FUNPOW_EQ_LINV
   Only-if part: y = FUNPOW (LINV f s) n x) ==> x = FUNPOW f n y
        FUNPOW f n y
      = FUNPOW f n (FUNPOW (LINV f s) n x))   by y = FUNPOW (LINV f s) n x)
      = x                                     by FUNPOW_LINV_EQ
*)
Theorem FUNPOW_LINV_INV:
  !f s x y n. f PERMUTES s /\ x IN s /\ y IN s ==>
              (x = FUNPOW f n y <=> y = FUNPOW (LINV f s) n x)
Proof
  rw[EQ_IMP_THM] >-
  rw[FUNPOW_EQ_LINV] >>
  rw[FUNPOW_LINV_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* FUNPOW with incremental cons.                                             *)
(* ------------------------------------------------------------------------- *)

(* Note from HelperList: m downto n = REVERSE [m .. n] *)

(* Idea: when applying incremental cons (f head) to a list for n times,
         head of the result is f^n (head of list). *)

(* Theorem: HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls) *)
(* Proof:
   Let h = (\ls. f (HD ls)::ls).
   By induction on n.
   Base: !ls. HD (FUNPOW h 0 ls) = FUNPOW f 0 (HD ls)
           HD (FUNPOW h 0 ls)
         = HD ls                by FUNPOW_0
         = FUNPOW f 0 (HD ls)   by FUNPOW_0
   Step: !ls. HD (FUNPOW h n ls) = FUNPOW f n (HD ls) ==>
         !ls. HD (FUNPOW h (SUC n) ls) = FUNPOW f (SUC n) (HD ls)
           HD (FUNPOW h (SUC n) ls)
         = HD (FUNPOW h n (h ls))    by FUNPOW
         = FUNPOW f n (HD (h ls))    by induction hypothesis
         = FUNPOW f n (f (HD ls))    by definition of h
         = FUNPOW f (SUC n) (HD ls)  by FUNPOW
*)
Theorem FUNPOW_cons_head:
  !f n ls. HD (FUNPOW (\ls. f (HD ls)::ls) n ls) = FUNPOW f n (HD ls)
Proof
  strip_tac >>
  qabbrev_tac `h = \ls. f (HD ls)::ls` >>
  Induct >-
  simp[] >>
  rw[FUNPOW, Abbr`h`]
QED

(* Idea: when applying incremental cons (f head) to a singleton [u] for n times,
         the result is the list [f^n(u), .... f(u), u]. *)

(* Theorem: FUNPOW (\ls. f (HD ls)::ls) n [u] =
            MAP (\j. FUNPOW f j u) (n downto 0) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [u] = MAP h (0 downto 0)
           FUNPOW g 0 [u]
         = [u]                       by FUNPOW_0
         = [FUNPOW f 0 u]            by FUNPOW_0
         = MAP h [0]                 by MAP
         = MAP h (0 downto 0)  by REVERSE
   Step: FUNPOW g n [u] = MAP h (n downto 0) ==>
         FUNPOW g (SUC n) [u] = MAP h (SUC n downto 0)
           FUNPOW g (SUC n) [u]
         = g (FUNPOW g n [u])             by FUNPOW_SUC
         = g (MAP h (n downto 0))   by induction hypothesis
         = f (HD (MAP h (n downto 0))) ::
             MAP h (n downto 0)     by definition of g
         Now f (HD (MAP h (n downto 0)))
           = f (HD (MAP h (MAP (\x. n - x) [0 .. n])))    by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n - x) [0 .. n]))        by MAP_COMPOSE
           = f ((h o (\x. n - x)) 0)                      by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 0)
           = MAP h ((n + 1) :: (n downto 0))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [0 .. n]))   by REVERSE_SNOC
           = MAP h (SUC n downto 0)                  by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_0:
  !f u n. FUNPOW (\ls. f (HD ls)::ls) n [u] =
          MAP (\j. FUNPOW f j u) (n downto 0)
Proof
  ntac 2 strip_tac >>
  Induct >-
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  rw[] >>
  `f (HD (MAP h (n downto 0))) = h (n + 1)` by
  (`[0 .. n] = 0 :: [1 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `FUNPOW g (SUC n) [u] = g (FUNPOW g n [u])` by rw[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 0))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 0)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 0))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [0 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* Idea: when applying incremental cons (f head) to a singleton [f(u)] for (n-1) times,
         the result is the list [f^n(u), .... f(u)]. *)

(* Theorem: 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
            MAP (\j. FUNPOW f j u) (n downto 1)) *)
(* Proof:
   Let g = (\ls. f (HD ls)::ls),
       h = (\j. FUNPOW f j u).
   By induction on n.
   Base: FUNPOW g 0 [f u] = MAP h (REVERSE [1 .. 1])
           FUNPOW g 0 [f u]
         = [f u]                     by FUNPOW_0
         = [FUNPOW f 1 u]            by FUNPOW_1
         = MAP h [1]                 by MAP
         = MAP h (REVERSE [1 .. 1])  by REVERSE
   Step: 0 < n ==> FUNPOW g (n-1) [f u] = MAP h (n downto 1) ==>
         FUNPOW g n [f u] = MAP h (REVERSE [1 .. SUC n])
         The case n = 0 is the base case. For n <> 0,
           FUNPOW g n [f u]
         = g (FUNPOW g (n-1) [f u])       by FUNPOW_SUC
         = g (MAP h (n downto 1))         by induction hypothesis
         = f (HD (MAP h (n downto 1))) ::
             MAP h (n downto 1)           by definition of g
         Now f (HD (MAP h (n downto 1)))
           = f (HD (MAP h (MAP (\x. n + 1 - x) [1 .. n])))  by listRangeINC_REVERSE
           = f (HD (MAP h o (\x. n + 1 - x) [1 .. n]))      by MAP_COMPOSE
           = f ((h o (\x. n + 1 - x)) 1)                    by MAP
           = f (h n)
           = f (FUNPOW f n u)             by definition of h
           = FUNPOW (n + 1) u             by FUNPOW_SUC
           = h (n + 1)                    by definition of h
          so h (n + 1) :: MAP h (n downto 1)
           = MAP h ((n + 1) :: (n downto 1))         by MAP
           = MAP h (REVERSE (SNOC (n+1) [1 .. n]))   by REVERSE_SNOC
           = MAP h (REVERSE [1 .. SUC n])            by listRangeINC_SNOC
*)
Theorem FUNPOW_cons_eq_map_1:
  !f u n. 0 < n ==> (FUNPOW (\ls. f (HD ls)::ls) (n - 1) [f u] =
          MAP (\j. FUNPOW f j u) (n downto 1))
Proof
  ntac 2 strip_tac >>
  Induct >-
  simp[] >>
  rw[] >>
  qabbrev_tac `g = \ls. f (HD ls)::ls` >>
  qabbrev_tac `h = \j. FUNPOW f j u` >>
  Cases_on `n = 0` >-
  rw[Abbr`g`, Abbr`h`] >>
  `f (HD (MAP h (n downto 1))) = h (n + 1)` by
  (`[1 .. n] = 1 :: [2 .. n]` by rw[listRangeINC_CONS] >>
  fs[listRangeINC_REVERSE, MAP_COMPOSE, GSYM FUNPOW_SUC, ADD1, Abbr`h`]) >>
  `n = SUC (n-1)` by decide_tac >>
  `FUNPOW g n [f u] = g (FUNPOW g (n - 1) [f u])` by metis_tac[FUNPOW_SUC] >>
  `_ = g (MAP h (n downto 1))` by fs[] >>
  `_ = h (n + 1) :: MAP h (n downto 1)` by rw[Abbr`g`] >>
  `_ = MAP h ((n + 1) :: (n downto 1))` by rw[] >>
  `_ = MAP h (REVERSE (SNOC (n+1) [1 .. n]))` by rw[REVERSE_SNOC] >>
  rw[listRangeINC_SNOC, ADD1]
QED

(* ------------------------------------------------------------------------- *)
(* Integer Functions.                                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Factorial                                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: FACT 0 = 1 *)
(* Proof: by FACT *)
val FACT_0 = store_thm(
  "FACT_0",
  ``FACT 0 = 1``,
  EVAL_TAC);

(* Theorem: FACT 1 = 1 *)
(* Proof:
     FACT 1
   = FACT (SUC 0)      by ONE
   = (SUC 0) * FACT 0  by FACT
   = (SUC 0) * 1       by FACT
   = 1                 by ONE
*)
val FACT_1 = store_thm(
  "FACT_1",
  ``FACT 1 = 1``,
  EVAL_TAC);

(* Theorem: FACT 2 = 2 *)
(* Proof:
     FACT 2
   = FACT (SUC 1)      by TWO
   = (SUC 1) * FACT 1  by FACT
   = (SUC 1) * 1       by FACT_1
   = 2                 by TWO
*)
val FACT_2 = store_thm(
  "FACT_2",
  ``FACT 2 = 2``,
  EVAL_TAC);

(* Theorem: (FACT n = 1) <=> n <= 1 *)
(* Proof:
   If n = 0,
      LHS = (FACT 0 = 1) = T         by FACT_0
      RHS = 0 <= 1 = T               by arithmetic
   If n <> 0, n = SUC m              by num_CASES
      LHS = FACT (SUC m) = 1
        <=> (SUC m) * FACT m = 1     by FACT
        <=> SUC m = 1 /\ FACT m = 1  by  MULT_EQ_1
        <=> m = 0  /\ FACT m = 1     by m = PRE 1 = 0
        <=> m = 0                    by FACT_0
      RHS = SUC m <= 1
        <=> ~(1 <= m)                by NOT_LEQ
        <=> m < 1                    by NOT_LESS_EQUAL
        <=> m = 0                    by arithmetic
*)
val FACT_EQ_1 = store_thm(
  "FACT_EQ_1",
  ``!n. (FACT n = 1) <=> n <= 1``,
  rpt strip_tac >>
  Cases_on `n` >>
  rw[FACT_0] >>
  rw[FACT] >>
  `!m. SUC m <= 1 <=> (m = 0)` by decide_tac >>
  metis_tac[FACT_0]);

(* Theorem: 1 <= FACT n *)
(* Proof:
   Note 0 < FACT n    by FACT_LESS
     so 1 <= FACT n   by arithmetic
*)
val FACT_GE_1 = store_thm(
  "FACT_GE_1",
  ``!n. 1 <= FACT n``,
  metis_tac[FACT_LESS, LESS_OR, ONE]);

(* Theorem: (FACT n = n) <=> (n = 1) \/ (n = 2) *)
(* Proof:
   If part: (FACT n = n) ==> (n = 1) \/ (n = 2)
      Note n <> 0           by FACT_0: FACT 0 = 1
       ==> ?m. n = SUC m    by num_CASES
      Thus SUC m * FACT m = SUC m       by FACT
                          = SUC m * 1   by MULT_RIGHT_1
       ==> FACT m = 1                   by EQ_MULT_LCANCEL, SUC_NOT
        or m <= 1           by FACT_EQ_1
      Thus m = 0 or 1       by arithmetic
        or n = 1 or 2       by ONE, TWO

   Only-if part: (FACT 1 = 1) /\ (FACT 2 = 2)
      Note FACT 1 = 1       by FACT_1
       and FACT 2 = 2       by FACT_2
*)
val FACT_EQ_SELF = store_thm(
  "FACT_EQ_SELF",
  ``!n. (FACT n = n) <=> (n = 1) \/ (n = 2)``,
  rw[EQ_IMP_THM] >| [
    `n <> 0` by metis_tac[FACT_0, DECIDE``1 <> 0``] >>
    `?m. n = SUC m` by metis_tac[num_CASES] >>
    fs[FACT] >>
    `FACT m = 1` by metis_tac[MULT_LEFT_1, EQ_MULT_RCANCEL, SUC_NOT] >>
    `m <= 1` by rw[GSYM FACT_EQ_1] >>
    decide_tac,
    rw[FACT_1],
    rw[FACT_2]
  ]);

(* Theorem: 0 < n ==> n <= FACT n *)
(* Proof:
   Note n <> 0             by 0 < n
    ==> ?m. n = SUC m      by num_CASES
   Thus FACT n
      = FACT (SUC m)       by n = SUC m
      = (SUC m) * FACT m   by FACT_LESS: 0 < FACT m
      >= (SUC m)           by LE_MULT_CANCEL_LBARE
      >= n                 by n = SUC m
*)
val FACT_GE_SELF = store_thm(
  "FACT_GE_SELF",
  ``!n. 0 < n ==> n <= FACT n``,
  rpt strip_tac >>
  `?m. n = SUC m` by metis_tac[num_CASES, NOT_ZERO_LT_ZERO] >>
  rw[FACT] >>
  rw[FACT_LESS]);

(* Theorem: 0 < n ==> (FACT (n-1) = FACT n DIV n) *)
(* Proof:
   Since  n = SUC(n-1)                 by SUC_PRE, 0 < n.
     and  FACT n = n * FACT (n-1)      by FACT
                 = FACT (n-1) * n      by MULT_COMM
                 = FACT (n-1) * n + 0  by ADD_0
   Hence  FACT (n-1) = FACT n DIV n    by DIV_UNIQUE, 0 < n.
*)
val FACT_DIV = store_thm(
  "FACT_DIV",
  ``!n. 0 < n ==> (FACT (n-1) = FACT n DIV n)``,
  rpt strip_tac >>
  `n = SUC(n-1)` by decide_tac >>
  `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
  `_ = FACT (n-1) * n + 0` by rw[MULT_COMM] >>
  metis_tac[DIV_UNIQUE]);

(* Theorem: n! = PROD_SET (count (n+1))  *)
(* Proof: by induction on n.
   Base case: FACT 0 = PROD_SET (IMAGE SUC (count 0))
     LHS = FACT 0
         = 1                               by FACT
         = PROD_SET {}                     by PROD_SET_THM
         = PROD_SET (IMAGE SUC {})         by IMAGE_EMPTY
         = PROD_SET (IMAGE SUC (count 0))  by COUNT_ZERO
         = RHS
   Step case: FACT n = PROD_SET (IMAGE SUC (count n)) ==>
              FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n)))
     Note: (SUC n) NOTIN (IMAGE SUC (count n))  by IN_IMAGE, IN_COUNT [1]
     LHS = FACT (SUC n)
         = (SUC n) * (FACT n)                            by FACT
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)))    by induction hypothesis
         = (SUC n) * (PROD_SET (IMAGE SUC (count n)) DELETE (SUC n))         by DELETE_NON_ELEMENT, [1]
         = PROD_SET ((SUC n) INSERT ((IMAGE SUC (count n)) DELETE (SUC n)))  by PROD_SET_THM
         = PROD_SET (IMAGE SUC (n INSERT (count n)))     by IMAGE_INSERT
         = PROD_SET (IMAGE SUC (count (SUC n)))          by COUNT_SUC
         = RHS
*)
val FACT_EQ_PROD = store_thm(
  "FACT_EQ_PROD",
  ``!n. FACT n = PROD_SET (IMAGE SUC (count n))``,
  Induct_on `n` >-
  rw[PROD_SET_THM, FACT] >>
  rw[PROD_SET_THM, FACT, COUNT_SUC] >>
  `(SUC n) NOTIN (IMAGE SUC (count n))` by rw[] >>
  metis_tac[DELETE_NON_ELEMENT]);

(* Theorem: n!/m! = product of (m+1) to n.
            m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m)) *)
(* Proof: by factorial formula.
   By induction on n.
   Base case: m < 0 ==> ...
     True since m < 0 = F.
   Step case: !m. m < n ==>
              (FACT n = PROD_SET (IMAGE SUC (count n DIFF count m)) * FACT m) ==>
              !m. m < SUC n ==>
              (FACT (SUC n) = PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m)
     Note that m < SUC n ==> m <= n.
      and FACT (SUC n) = (SUC n) * FACT n     by FACT
     If m = n,
        PROD_SET (IMAGE SUC (count (SUC n) DIFF count n)) * FACT n
      = PROD_SET (IMAGE SUC {n}) * FACT n     by IN_DIFF, IN_COUNT
      = PROD_SET {SUC n} * FACT n             by IN_IMAGE
      = (SUC n) * FACT n                      by PROD_SET_THM
     If m < n,
        n NOTIN (count m)                     by IN_COUNT
     so n INSERT ((count n) DIFF (count m))
      = (n INSERT (count n)) DIFF (count m)   by INSERT_DIFF
      = count (SUC n) DIFF (count m)          by EXTENSION
     Since (SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))  by IN_IMAGE, IN_DIFF, IN_COUNT
       and FINITE (IMAGE SUC ((count n) DIFF (count m)))         by IMAGE_FINITE, FINITE_DIFF, FINITE_COUNT
     Hence PROD_SET (IMAGE SUC (count (SUC n) DIFF count m)) * FACT m
         = ((SUC n) * PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m   by PROD_SET_IMAGE_REDUCTION
         = (SUC n) * (PROD_SET (IMAGE SUC (count n DIFF count m))) * FACT m)  by MULT_ASSOC
         = (SUC n) * FACT n                                      by induction hypothesis
         = FACT (SUC n)                                          by FACT
*)
val FACT_REDUCTION = store_thm(
  "FACT_REDUCTION",
  ``!n m. m < n ==> (FACT n = PROD_SET (IMAGE SUC ((count n) DIFF (count m))) * (FACT m))``,
  Induct_on `n` >-
  rw[] >>
  rw_tac std_ss[FACT] >>
  `m <= n` by decide_tac >>
  Cases_on `m = n` >| [
    rw_tac std_ss[] >>
    `count (SUC m) DIFF count m = {m}` by
  (rw[DIFF_DEF] >>
    rw[EXTENSION, EQ_IMP_THM]) >>
    `PROD_SET (IMAGE SUC {m}) = SUC m` by rw[PROD_SET_THM] >>
    metis_tac[],
    `m < n` by decide_tac >>
    `n NOTIN (count m)` by srw_tac[ARITH_ss][] >>
    `n INSERT ((count n) DIFF (count m)) = (n INSERT (count n)) DIFF (count m)` by rw[] >>
    `_ = count (SUC n) DIFF (count m)` by srw_tac[ARITH_ss][EXTENSION] >>
    `(SUC n) NOTIN (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    `FINITE (IMAGE SUC ((count n) DIFF (count m)))` by rw[] >>
    metis_tac[PROD_SET_IMAGE_REDUCTION, MULT_ASSOC]
  ]);

(* Theorem: prime p ==> p cannot divide k! for p > k.
            prime p /\ k < p ==> ~(p divides (FACT k)) *)
(* Proof:
   Since all terms of k! are less than p, and p has only 1 and p as factor.
   By contradiction, and induction on k.
   Base case: prime p ==> 0 < p ==> p divides (FACT 0) ==> F
     Since FACT 0 = 1              by FACT
       and p divides 1 <=> p = 1   by DIVIDES_ONE
       but prime p ==> 1 < p       by ONE_LT_PRIME
       so this is a contradiction.
   Step case: prime p /\ k < p ==> p divides (FACT k) ==> F ==>
              SUC k < p ==> p divides (FACT (SUC k)) ==> F
     Since FACT (SUC k) = SUC k * FACT k    by FACT
       and prime p /\ p divides (FACT (SUC k))
       ==> p divides (SUC k),
        or p divides (FACT k)               by P_EUCLIDES
     But SUC k < p, so ~(p divides (SUC k)) by NOT_LT_DIVIDES
     Hence p divides (FACT k) ==> F         by induction hypothesis
*)
val PRIME_BIG_NOT_DIVIDES_FACT = store_thm(
  "PRIME_BIG_NOT_DIVIDES_FACT",
  ``!p k. prime p /\ k < p ==> ~(p divides (FACT k))``,
  (spose_not_then strip_assume_tac) >>
  Induct_on `k` >| [
    rw[FACT] >>
    metis_tac[ONE_LT_PRIME, LESS_NOT_EQ],
    rw[FACT] >>
    (spose_not_then strip_assume_tac) >>
    `k < p /\ 0 < SUC k` by decide_tac >>
    metis_tac[P_EUCLIDES, NOT_LT_DIVIDES]
  ]);

(* Idea: test if a function f is factorial. *)

(* Theorem: f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n *)
(* Proof:
   If part is true         by FACT
   Only-if part, apply FUN_EQ_THM, this is to show:
   !n. f n = FACT n.
   By induction on n.
   Base: f 0 = FACT 0
           f 0
         = 1               by given
         = FACT 0          by FACT_0
   Step: f n = FACT n ==> f (SUC n) = FACT (SUC n)
           f (SUC n)
         = SUC n * f n     by given
         = SUC n * FACT n  by induction hypothesis
         = FACT (SUC n)    by FACT
*)
Theorem FACT_iff:
  !f. f = FACT <=> f 0 = 1 /\ !n. f (SUC n) = SUC n * f n
Proof
  rw[FACT, EQ_IMP_THM] >>
  rw[FUN_EQ_THM] >>
  Induct_on `x` >>
  simp[FACT]
QED

(* ------------------------------------------------------------------------- *)
(* Basic GCD, LCM Theorems                                                   *)
(* ------------------------------------------------------------------------- *)

(* Note: gcd Theory has: GCD_SYM   |- !a b. gcd a b = gcd b a
                    but: LCM_COMM  |- lcm a b = lcm b a
*)
val GCD_COMM = save_thm("GCD_COMM", GCD_SYM);
(* val GCD_COMM = |- !a b. gcd a b = gcd b a: thm *)
val LCM_SYM = save_thm("LCM_SYM", LCM_COMM |> GEN ``b:num`` |> GEN ``a:num``);
(* val val LCM_SYM = |- !a b. lcm a b = lcm b a: thm *)

(* Note:
gcdTheory.LCM_0  |- (lcm 0 x = 0) /\ (lcm x 0 = 0)
gcdTheory.LCM_1  |- (lcm 1 x = x) /\ (lcm x 1 = x)
gcdTheory.GCD_1  |- coprime 1 x /\ coprime x 1
but only GCD_0L, GCD_0R
gcdTheory.GCD_EQ_0 |- !n m. (gcd n m = 0) <=> (n = 0) /\ (m = 0)
*)

(* Theorem: (gcd 0 x = x) /\ (gcd x 0 = x) *)
(* Proof: by GCD_0L, GCD_0R *)
val GCD_0 = store_thm(
  "GCD_0",
  ``!x. (gcd 0 x = x) /\ (gcd x 0 = x)``,
  rw_tac std_ss[GCD_0L, GCD_0R]);

(* Theorem: gcd(n, m) = 1 ==> n divides (c * m) ==> n divides c *)
(* Proof:
   This is L_EUCLIDES:  (Euclid's Lemma)
> val it = |- !a b c. coprime a b /\ divides b (a * c) ==> b divides c : thm
*)

(* Theorem: If 0 < n, 0 < m, let g = gcd n m, then 0 < g and n MOD g = 0 and m MOD g = 0 *)
(* Proof:
   0 < n ==> n <> 0, 0 < m ==> m <> 0,              by NOT_ZERO_LT_ZERO
   hence  g = gcd n m <> 0, or 0 < g.               by GCD_EQ_0
   g = gcd n m ==> (g divides n) /\ (g divides m)   by GCD_IS_GCD, is_gcd_def
               ==> (n MOD g = 0) /\ (m MOD g = 0)   by DIVIDES_MOD_0
*)
val GCD_DIVIDES = store_thm(
  "GCD_DIVIDES",
  ``!m n. 0 < n /\ 0 < m ==> 0 < (gcd n m) /\ (n MOD (gcd n m) = 0) /\ (m MOD (gcd n m) = 0)``,
  ntac 3 strip_tac >>
  conj_asm1_tac >-
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
  metis_tac[GCD_IS_GCD, is_gcd_def, DIVIDES_MOD_0]);

(* Theorem: gcd n (gcd n m) = gcd n m *)
(* Proof:
   If n = 0,
      gcd 0 (gcd n m) = gcd n m   by GCD_0L
   If m = 0,
      gcd n (gcd n 0)
    = gcd n n                     by GCD_0R
    = n = gcd n 0                 by GCD_REF
   If n <> 0, m <> 0, d <> 0      by GCD_EQ_0
   Since d divides n, n MOD d = 0
     gcd n d
   = gcd d n             by GCD_SYM
   = gcd (n MOD d) d     by GCD_EFFICIENTLY, d <> 0
   = gcd 0 d             by GCD_DIVIDES
   = d                   by GCD_0L
*)
val GCD_GCD = store_thm(
  "GCD_GCD",
  ``!m n. gcd n (gcd n m) = gcd n m``,
  rpt strip_tac >>
  Cases_on `n = 0` >- rw[] >>
  Cases_on `m = 0` >- rw[] >>
  `0 < n /\ 0 < m` by decide_tac >>
  metis_tac[GCD_SYM, GCD_EFFICIENTLY, GCD_DIVIDES, GCD_EQ_0, GCD_0L]);

(* Theorem: GCD m n * LCM m n = m * n *)
(* Proof:
   By lcm_def:
   lcm m n = if (m = 0) \/ (n = 0) then 0 else m * n DIV gcd m n
   If m = 0,
   gcd 0 n * lcm 0 n = n * 0 = 0 = 0 * n, hence true.
   If n = 0,
   gcd m 0 * lcm m 0 = m * 0 = 0 = m * 0, hence true.
   If m <> 0, n <> 0,
   gcd m n * lcm m n = gcd m n * (m * n DIV gcd m n) = m * n.
*)
val GCD_LCM = store_thm(
  "GCD_LCM",
  ``!m n. gcd m n * lcm m n = m * n``,
  rw[lcm_def] >>
  `0 < m /\ 0 < n` by decide_tac >>
  `0 < gcd m n /\ (n MOD gcd m n = 0)` by rw[GCD_DIVIDES] >>
  qabbrev_tac `d = gcd m n` >>
  `m * n = (m * n) DIV d * d + (m * n) MOD d` by rw[DIVISION] >>
  `(m * n) MOD d = 0` by metis_tac[MOD_TIMES2, ZERO_MOD, MULT_0] >>
  metis_tac[ADD_0, MULT_COMM]);

(* Theorem: m divides (lcm m n) /\ n divides (lcm m n) *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_DIVISORS = store_thm(
  "LCM_DIVISORS",
  ``!m n. m divides (lcm m n) /\ n divides (lcm m n)``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: m divides p /\ n divides p ==> (lcm m n) divides p *)
(* Proof: by LCM_IS_LEAST_COMMON_MULTIPLE *)
val LCM_IS_LCM = store_thm(
  "LCM_IS_LCM",
  ``!m n p. m divides p /\ n divides p ==> (lcm m n) divides p``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE]);

(* Theorem: (lcm m n = 0) <=> ((m = 0) \/ (n = 0)) *)
(* Proof:
   If part: lcm m n = 0 ==> m = 0 \/ n = 0
      By contradiction, suppse m = 0 /\ n = 0.
      Then gcd m n = 0                     by GCD_EQ_0
       and m * n = 0                       by MULT_EQ_0
       but (gcd m n) * (lcm m n) = m * n   by GCD_LCM
        so RHS <> 0, but LHS = 0           by MULT_0
       This is a contradiction.
   Only-if part: m = 0 \/ n = 0 ==> lcm m n = 0
      True by LCM_0
*)
val LCM_EQ_0 = store_thm(
  "LCM_EQ_0",
  ``!m n. (lcm m n = 0) <=> ((m = 0) \/ (n = 0))``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `(gcd m n) * (lcm m n) = m * n` by rw[GCD_LCM] >>
    `gcd m n <> 0` by rw[GCD_EQ_0] >>
    `m * n <> 0` by rw[MULT_EQ_0] >>
    metis_tac[MULT_0],
    rw[LCM_0],
    rw[LCM_0]
  ]);

(* Note: gcdTheory.GCD_REF |- !a. gcd a a = a *)

(* Theorem: lcm a a = a *)
(* Proof:
  If a = 0,
     lcm 0 0 = 0                      by LCM_0
  If a <> 0,
     (gcd a a) * (lcm a a) = a * a    by GCD_LCM
             a * (lcm a a) = a * a    by GCD_REF
                   lcm a a = a        by MULT_LEFT_CANCEL, a <> 0
*)
val LCM_REF = store_thm(
  "LCM_REF",
  ``!a. lcm a a = a``,
  metis_tac[num_CASES, LCM_0, GCD_LCM, GCD_REF, MULT_LEFT_CANCEL]);

(* Theorem: a divides n /\ b divides n ==> (lcm a b) divides n *)
(* Proof: same as LCM_IS_LCM *)
val LCM_DIVIDES = store_thm(
  "LCM_DIVIDES",
  ``!n a b. a divides n /\ b divides n ==> (lcm a b) divides n``,
  rw[LCM_IS_LCM]);
(*
> LCM_IS_LCM |> ISPEC ``a:num`` |> ISPEC ``b:num`` |> ISPEC ``n:num`` |> GEN_ALL;
val it = |- !n b a. a divides n /\ b divides n ==> lcm a b divides n: thm
*)

(* Theorem: 0 < m \/ 0 < n ==> 0 < gcd m n *)
(* Proof: by GCD_EQ_0, NOT_ZERO_LT_ZERO *)
val GCD_POS = store_thm(
  "GCD_POS",
  ``!m n. 0 < m \/ 0 < n ==> 0 < gcd m n``,
  metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m /\ 0 < n ==> 0 < lcm m n *)
(* Proof: by LCM_EQ_0, NOT_ZERO_LT_ZERO *)
val LCM_POS = store_thm(
  "LCM_POS",
  ``!m n. 0 < m /\ 0 < n ==> 0 < lcm m n``,
  metis_tac[LCM_EQ_0, NOT_ZERO_LT_ZERO]);

(* Theorem: n divides m <=> gcd n m = n *)
(* Proof:
   If part:
     n divides m ==> ?k. m = k * n   by divides_def
       gcd n m
     = gcd n (k * n)
     = gcd (n * 1) (n * k)      by MULT_RIGHT_1, MULT_COMM
     = n * gcd 1 k              by GCD_COMMON_FACTOR
     = n * 1                    by GCD_1
     = n                        by MULT_RIGHT_1
   Only-if part: gcd n m = n ==> n divides m
     If n = 0, gcd 0 m = m      by GCD_0L
     But gcd n m = n = 0        by givien
     hence m = 0,
     and 0 divides 0 is true    by DIVIDES_REFL
     If n <> 0,
       If m = 0, LHS true       by GCD_0R
                 RHS true       by ALL_DIVIDES_0
       If m <> 0,
       then 0 < n and 0 < m,
       gcd n m = gcd (m MOD n) n       by GCD_EFFICIENTLY
       if (m MOD n) = 0
          then n divides m             by DIVIDES_MOD_0
       If (m MOD n) <> 0,
       so (m MOD n) MOD (gcd n m) = 0  by GCD_DIVIDES
       or (m MOD n) MOD n = 0          by gcd n m = n, given
       or  m MOD n = 0                 by MOD_MOD
       contradicting (m MOD n) <> 0, hence true.
*)
val divides_iff_gcd_fix = store_thm(
  "divides_iff_gcd_fix",
  ``!m n. n divides m <=> (gcd n m = n)``,
  rw[EQ_IMP_THM] >| [
    `?k. m = k * n` by rw[GSYM divides_def] >>
    `gcd n m = gcd (n * 1) (n * k)` by rw[MULT_COMM] >>
    rw[GCD_COMMON_FACTOR, GCD_1],
    Cases_on `n = 0` >-
    metis_tac[GCD_0L, DIVIDES_REFL] >>
    Cases_on `m = 0` >-
    metis_tac[GCD_0R, ALL_DIVIDES_0] >>
    `0 < n /\ 0 < m` by decide_tac >>
    Cases_on `m MOD n = 0` >-
    metis_tac[DIVIDES_MOD_0] >>
    `0 < m MOD n` by decide_tac >>
    metis_tac[GCD_EFFICIENTLY, GCD_DIVIDES, MOD_MOD]
  ]);

(* Theorem: !m n. n divides m <=> (lcm n m = m) *)
(* Proof:
   If n = 0,
      n divides m <=> m = 0         by ZERO_DIVIDES
      and lcm 0 0 = 0 = m           by LCM_0
   If n <> 0,
     gcd n m * lcm n m = n * m      by GCD_LCM
     If part: n divides m ==> (lcm n m = m)
        Then gcd n m = n            by divides_iff_gcd_fix
        so   n * lcm n m = n * m    by above
                 lcm n m = m        by MULT_LEFT_CANCEL, n <> 0
     Only-if part: lcm n m = m ==> n divides m
        If m = 0, n divdes 0 = true by ALL_DIVIDES_0
        If m <> 0,
        Then gcd n m * m = n * m    by above
          or     gcd n m = n        by MULT_RIGHT_CANCEL, m <> 0
          so     n divides m        by divides_iff_gcd_fix
*)
val divides_iff_lcm_fix = store_thm(
  "divides_iff_lcm_fix",
  ``!m n. n divides m <=> (lcm n m = m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[ZERO_DIVIDES, LCM_0] >>
  metis_tac[GCD_LCM, MULT_LEFT_CANCEL, MULT_RIGHT_CANCEL, divides_iff_gcd_fix, ALL_DIVIDES_0]);

(* Theorem: If prime p divides n, ?m. 0 < m /\ (p ** m) divides n /\ n DIV (p ** m) has no p *)
(* Proof:
   Let s = {j | (p ** j) divides n }
   Since p ** 1 = p, 1 IN s, so s <> {}.
       (p ** j) divides n
   ==> p ** j <= n                  by DIVIDES_LE
   ==> p ** j <= p ** z             by EXP_ALWAYS_BIG_ENOUGH
   ==>      j <= z                  by EXP_BASE_LE_MONO
   ==> s SUBSET count (SUC z),
   so FINITE s                      by FINITE_COUNT, SUBSET_FINITE
   Let m = MAX_SET s,
   m IN s, so (p ** m) divides n    by MAX_SET_DEF
   1 <= m, or 0 < m.
   ?q. n = q * (p ** m)             by divides_def
   To prove: !k. gcd (p ** k) (n DIV (p ** m)) = 1
   By contradiction, suppose there is a k such that
   gcd (p ** k) (n DIV (p ** m)) <> 1
   So there is a prime pp that divides this gcd, by PRIME_FACTOR
   but pp | p ** k, a pure prime, so pp = p      by DIVIDES_EXP_BASE, prime_divides_only_self
       pp | n DIV (p ** m)
   or  pp * p ** m | n
       p * SUC m | n, making m not MAX_SET s.
*)
val FACTOR_OUT_PRIME = store_thm(
  "FACTOR_OUT_PRIME",
  ``!n p. 0 < n /\ prime p /\ p divides n ==> ?m. 0 < m /\ (p ** m) divides n /\ !k. gcd (p ** k) (n DIV (p ** m)) = 1``,
  rpt strip_tac >>
  qabbrev_tac `s = {j | (p ** j) divides n }` >>
  `!j. j IN s <=> (p ** j) divides n` by rw[Abbr`s`] >>
  `p ** 1 = p` by rw[] >>
  `1 IN s` by metis_tac[] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  `?z. n <= p ** z` by rw[EXP_ALWAYS_BIG_ENOUGH] >>
  `!j. j IN s ==> p ** j <= n` by metis_tac[DIVIDES_LE] >>
  `!j. j IN s ==> p ** j <= p ** z` by metis_tac[LESS_EQ_TRANS] >>
  `!j. j IN s ==> j <= z` by metis_tac[EXP_BASE_LE_MONO] >>
  `!j. j <= z <=> j < SUC z` by decide_tac >>
  `!j. j < SUC z <=> j IN count (SUC z)` by rw[] >>
  `s SUBSET count (SUC z)` by metis_tac[SUBSET_DEF] >>
  `FINITE s` by metis_tac[FINITE_COUNT, SUBSET_FINITE] >>
  `s <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  qabbrev_tac `m = MAX_SET s` >>
  `m IN s /\ !y. y IN s ==> y <= m`by rw[MAX_SET_DEF, Abbr`m`] >>
  qexists_tac `m` >>
  CONJ_ASM1_TAC >| [
    `1 <= m` by metis_tac[] >>
    decide_tac,
    CONJ_ASM1_TAC >-
    metis_tac[] >>
    qabbrev_tac `pm = p ** m` >>
    `0 < p` by decide_tac >>
    `0 < pm` by rw[ZERO_LT_EXP, Abbr`pm`] >>
    `n MOD pm = 0` by metis_tac[DIVIDES_MOD_0] >>
    `n = n DIV pm * pm` by metis_tac[DIVISION, ADD_0] >>
    qabbrev_tac `qm = n DIV pm` >>
    spose_not_then strip_assume_tac >>
    `?q. prime q /\ q divides (gcd (p ** k) qm)` by rw[PRIME_FACTOR] >>
    `0 <> pm /\ n <> 0` by decide_tac >>
    `qm <> 0` by metis_tac[MULT] >>
    `0 < qm` by decide_tac >>
    qabbrev_tac `pk = p ** k` >>
    `0 < pk` by rw[ZERO_LT_EXP, Abbr`pk`] >>
    `(gcd pk qm) divides pk /\ (gcd pk qm) divides qm` by metis_tac[GCD_DIVIDES, DIVIDES_MOD_0] >>
    `q divides pk /\ q divides qm` by metis_tac[DIVIDES_TRANS] >>
    `k <> 0` by metis_tac[EXP, GCD_1] >>
    `0 < k` by decide_tac >>
    `q divides p` by metis_tac[DIVIDES_EXP_BASE] >>
    `q = p` by rw[prime_divides_only_self] >>
    `?x. qm = x * q` by rw[GSYM divides_def] >>
    `n = x * p * pm` by metis_tac[] >>
    `_ = x * (p * pm)` by rw_tac arith_ss[] >>
    `_ = x * (p ** SUC m)` by rw[EXP, Abbr`pm`] >>
    `(p ** SUC m) divides n` by metis_tac[divides_def] >>
    `SUC m <= m` by metis_tac[] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Consequences of Coprime.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: If 1 < n, !x. coprime n x ==> 0 < x /\ 0 < x MOD n *)
(* Proof:
   If x = 0, gcd n x = n. But n <> 1, hence x <> 0, or 0 < x.
   x MOD n = 0 ==> x a multiple of n ==> gcd n x = n <> 1  if n <> 1.
   Hence if 1 < n, coprime n x ==> x MOD n <> 0, or 0 < x MOD n.
*)
val MOD_NONZERO_WHEN_GCD_ONE = store_thm(
  "MOD_NONZERO_WHEN_GCD_ONE",
  ``!n. 1 < n ==> !x. coprime n x ==> 0 < x /\ 0 < x MOD n``,
  ntac 4 strip_tac >>
  conj_asm1_tac >| [
    `1 <> n` by decide_tac >>
    `x <> 0` by metis_tac[GCD_0R] >>
    decide_tac,
    `1 <> n /\ x <> 0` by decide_tac >>
    `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
    `(k*x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
    spose_not_then strip_assume_tac >>
    `(x MOD n = 0) /\ 0 < n /\ 1 <> 0` by decide_tac >>
    metis_tac[MOD_MULITPLE_ZERO, MULT_COMM]
  ]);

(* Theorem: coprime n x /\ coprime n y ==> coprime n (x * y) *)
(* Proof:
   gcd n x = 1 ==> no common factor between x and n
   gcd n y = 1 ==> no common factor between y and n
   Hence there is no common factor between (x * y) and n, or gcd n (x * y) = 1

   gcd n (x * y) = gcd n y     by GCD_CANCEL_MULT, since coprime n x.
                 = 1           by given
*)
val PRODUCT_WITH_GCD_ONE = store_thm(
  "PRODUCT_WITH_GCD_ONE",
  ``!n x y. coprime n x /\ coprime n y ==> coprime n (x * y)``,
  metis_tac[GCD_CANCEL_MULT]);

(* Theorem: For 0 < n, coprime n x ==> coprime n (x MOD n) *)
(* Proof:
   Since n <> 0,
   1 = gcd n x            by given
     = gcd (x MOD n) n    by GCD_EFFICIENTLY
     = gcd n (x MOD n)    by GCD_SYM
*)
val MOD_WITH_GCD_ONE = store_thm(
  "MOD_WITH_GCD_ONE",
  ``!n x. 0 < n /\ coprime n x ==> coprime n (x MOD n)``,
  rpt strip_tac >>
  `0 <> n` by decide_tac >>
  metis_tac[GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: If 1 < n, coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k *)
(* Proof:
       gcd n x = 1 ==> x <> 0               by GCD_0R
   Also,
       gcd n x = 1
   ==> ?k q. k * x = q * n + 1              by LINEAR_GCD
   ==> (k * x) MOD n = (q * n + 1) MOD n    by arithmetic
   ==> (k * x) MOD n = 1                    by MOD_MULT, 1 < n.

   Let g = gcd n k.
   Since 1 < n, 0 < n.
   Since q * n+1 <> 0, x <> 0, k <> 0, hence 0 < k.
   Hence 0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)    by GCD_DIVIDES.
   Or  n = a * g /\ k = b * g    for some a, b.
   Therefore:
        (b * g) * x = q * (a * g) + 1
        (b * x) * g = (q * a) * g + 1      by arithmetic
   Hence g divides 1, or g = 1     since 0 < g.
*)
val GCD_ONE_PROPERTY = store_thm(
  "GCD_ONE_PROPERTY",
  ``!n x. 1 < n /\ coprime n x ==> ?k. ((k * x) MOD n = 1) /\ coprime n k``,
  rpt strip_tac >>
  `n <> 1` by decide_tac >>
  `x <> 0` by metis_tac[GCD_0R] >>
  `?k q. k * x = q * n + 1` by metis_tac[LINEAR_GCD] >>
  `(k * x) MOD n = 1` by rw_tac std_ss[MOD_MULT] >>
  `?g. g = gcd n k` by rw[] >>
  `n <> 0 /\ q*n + 1 <> 0` by decide_tac >>
  `k <> 0` by metis_tac[MULT_EQ_0] >>
  `0 < g /\ (n MOD g = 0) /\ (k MOD g = 0)` by metis_tac[GCD_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `g divides n /\ g divides k` by rw[DIVIDES_MOD_0] >>
  `g divides (n * q) /\ g divides (k*x)` by rw[DIVIDES_MULT] >>
  `g divides (n * q + 1)` by metis_tac [MULT_COMM] >>
  `g divides 1` by metis_tac[DIVIDES_ADD_2] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: For 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
            ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1) *)
(* Proof:
       gcd n x = 1
   ==> ?k. (k * x) MOD n = 1 /\ coprime n k   by GCD_ONE_PROPERTY
       (k * x) MOD n = 1
   ==> (k MOD n * x MOD n) MOD n = 1          by MOD_TIMES2
   ==> ((k MOD n) * x) MOD n = 1              by LESS_MOD, x < n.

   Now   k MOD n < n                          by MOD_LESS
   and   0 < k MOD n                          by MOD_MULITPLE_ZERO and 1 <> 0.

   Hence take y = k MOD n, then 0 < y < n.
   and gcd n k = 1 ==> gcd n (k MOD n) = 1    by MOD_WITH_GCD_ONE.
*)
val GCD_MOD_MULT_INV = store_thm(
  "GCD_MOD_MULT_INV",
  ``!n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
      ?y. 0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  rpt strip_tac >>
  `?k. ((k * x) MOD n = 1) /\ coprime n k` by rw_tac std_ss[GCD_ONE_PROPERTY] >>
  `0 < n` by decide_tac >>
  `(k MOD n * x MOD n) MOD n = 1` by rw_tac std_ss[MOD_TIMES2] >>
  `((k MOD n) * x) MOD n = 1` by metis_tac[LESS_MOD] >>
  `k MOD n < n` by rw_tac std_ss[MOD_LESS] >>
  `1 <> 0` by decide_tac >>
  `0 <> k MOD n` by metis_tac[MOD_MULITPLE_ZERO] >>
  `0 < k MOD n` by decide_tac >>
  metis_tac[MOD_WITH_GCD_ONE]);

(* Convert this into an existence definition *)
val lemma = prove(
  ``!n x. ?y. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
              0 < y /\ y < n /\ coprime n y /\ ((y * x) MOD n = 1)``,
  metis_tac[GCD_MOD_MULT_INV]);

val GEN_MULT_INV_DEF = new_specification(
  "GEN_MULT_INV_DEF",
  ["GCD_MOD_MUL_INV"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] lemma);
(* > val GEN_MULT_INV_DEF =
    |- !n x. 1 < n /\ 0 < x /\ x < n /\ coprime n x ==>
       0 < GCD_MOD_MUL_INV n x /\ GCD_MOD_MUL_INV n x < n /\ coprime n (GCD_MOD_MUL_INV n x) /\
       ((GCD_MOD_MUL_INV n x * x) MOD n = 1) : thm *)

(* ------------------------------------------------------------------------- *)
(* More GCD and LCM Theorems                                                 *)
(* ------------------------------------------------------------------------- *)

(* Note:
gcdTheory.LCM_IS_LEAST_COMMON_MULTIPLE
|- m divides lcm m n /\ n divides lcm m n /\ !p. m divides p /\ n divides p ==> lcm m n divides p
gcdTheory.GCD_IS_GREATEST_COMMON_DIVISOR
|- !a b. gcd a b divides a /\ gcd a b divides b /\ !d. d divides a /\ d divides b ==> d divides gcd a b
*)

(* Theorem: (c = gcd a b) <=>
            c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c *)
(* Proof:
   By GCD_IS_GREATEST_COMMON_DIVISOR
       (gcd a b) divides a     [1]
   and (gcd a b) divides b     [2]
   and !p. p divides a /\ p divides b ==> p divides (gcd a b)   [3]
   Hence if part is true, and for the only-if part,
   We have c divides (gcd a b)   by [3] above,
       and (gcd a b) divides c   by [1], [2] and the given implication
   Therefore c = gcd a b         by DIVIDES_ANTISYM
*)
val GCD_PROPERTY = store_thm(
  "GCD_PROPERTY",
  ``!a b c. (c = gcd a b) <=>
   c divides a /\ c divides b /\ !x. x divides a /\ x divides b ==> x divides c``,
  rw[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: gcd a (gcd b c) = gcd (gcd a b) c *)
(* Proof:
   Since (gcd a (gcd b c)) divides a    by GCD_PROPERTY
         (gcd a (gcd b c)) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd a (gcd b c)) divides c    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides a    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides b    by GCD_PROPERTY, DIVIDES_TRANS
         (gcd (gcd a b) c) divides c    by GCD_PROPERTY
   We have
         (gcd (gcd a b) c) divides (gcd b c)           by GCD_PROPERTY
     and (gcd (gcd a b) c) divides (gcd a (gcd b c))   by GCD_PROPERTY
    Also (gcd a (gcd b c)) divides (gcd a b)           by GCD_PROPERTY
     and (gcd a (gcd b c)) divides (gcd (gcd a b) c)   by GCD_PROPERTY
   Therefore gcd a (gcd b c) = gcd (gcd a b) c         by DIVIDES_ANTISYM
*)
val GCD_ASSOC = store_thm(
  "GCD_ASSOC",
  ``!a b c. gcd a (gcd b c) = gcd (gcd a b) c``,
  rpt strip_tac >>
  `(gcd a (gcd b c)) divides a` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd a (gcd b c)) divides c` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides a` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides b` by metis_tac[GCD_PROPERTY, DIVIDES_TRANS] >>
  `(gcd (gcd a b) c) divides c` by metis_tac[GCD_PROPERTY] >>
  `(gcd (gcd a b) c) divides (gcd a (gcd b c))` by metis_tac[GCD_PROPERTY] >>
  `(gcd a (gcd b c)) divides (gcd (gcd a b) c)` by metis_tac[GCD_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With identity by GCD_1: (gcd 1 x = 1) /\ (gcd x 1 = 1)
   GCD forms a monoid in numbers.
*)

(* Theorem: gcd a (gcd b c) = gcd b (gcd a c) *)
(* Proof:
     gcd a (gcd b c)
   = gcd (gcd a b) c    by GCD_ASSOC
   = gcd (gcd b a) c    by GCD_SYM
   = gcd b (gcd a c)    by GCD_ASSOC
*)
val GCD_ASSOC_COMM = store_thm(
  "GCD_ASSOC_COMM",
  ``!a b c. gcd a (gcd b c) = gcd b (gcd a c)``,
  metis_tac[GCD_ASSOC, GCD_SYM]);

(* Theorem: (c = lcm a b) <=>
            a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x *)
(* Proof:
   By LCM_IS_LEAST_COMMON_MULTIPLE
       a divides (lcm a b)    [1]
   and b divides (lcm a b)    [2]
   and !p. a divides p /\ divides b p ==> divides (lcm a b) p  [3]
   Hence if part is true, and for the only-if part,
   We have c divides (lcm a b)   by implication and [1], [2]
       and (lcm a b) divides c   by [3]
   Therefore c = lcm a b         by DIVIDES_ANTISYM
*)
val LCM_PROPERTY = store_thm(
  "LCM_PROPERTY",
  ``!a b c. (c = lcm a b) <=>
   a divides c /\ b divides c /\ !x. a divides x /\ b divides x ==> c divides x``,
  rw[LCM_IS_LEAST_COMMON_MULTIPLE, DIVIDES_ANTISYM, EQ_IMP_THM]);

(* Theorem: lcm a (lcm b c) = lcm (lcm a b) c *)
(* Proof:
   Since a divides (lcm a (lcm b c))   by LCM_PROPERTY
         b divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm a (lcm b c))   by LCM_PROPERTY, DIVIDES_TRANS
         a divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         b divides (lcm (lcm a b) c)   by LCM_PROPERTY, DIVIDES_TRANS
         c divides (lcm (lcm a b) c)   by LCM_PROPERTY
   We have
         (lcm b c) divides (lcm (lcm a b) c)           by LCM_PROPERTY
     and (lcm a (lcm b c)) divides (lcm (lcm a b) c)   by LCM_PROPERTY
    Also (lcm a b) divides (lcm a (lcm b c))           by LCM_PROPERTY
     and (lcm (lcm a b) c) divides (lcm a (lcm b c))   by LCM_PROPERTY
    Therefore lcm a (lcm b c) = lcm (lcm a b) c        by DIVIDES_ANTISYM
*)
val LCM_ASSOC = store_thm(
  "LCM_ASSOC",
  ``!a b c. lcm a (lcm b c) = lcm (lcm a b) c``,
  rpt strip_tac >>
  `a divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  `b divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `a divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `b divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY, DIVIDES_TRANS] >>
  `c divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm a (lcm b c)) divides (lcm (lcm a b) c)` by metis_tac[LCM_PROPERTY] >>
  `(lcm (lcm a b) c) divides (lcm a (lcm b c))` by metis_tac[LCM_PROPERTY] >>
  rw[DIVIDES_ANTISYM]);

(* Note:
   With the identity by LCM_0: (lcm 0 x = 0) /\ (lcm x 0 = 0)
   LCM forms a monoid in numbers.
*)

(* Theorem: lcm a (lcm b c) = lcm b (lcm a c) *)
(* Proof:
     lcm a (lcm b c)
   = lcm (lcm a b) c   by LCM_ASSOC
   = lcm (lcm b a) c   by LCM_COMM
   = lcm b (lcm a c)   by LCM_ASSOC
*)
val LCM_ASSOC_COMM = store_thm(
  "LCM_ASSOC_COMM",
  ``!a b c. lcm a (lcm b c) = lcm b (lcm a c)``,
  metis_tac[LCM_ASSOC, LCM_COMM]);

(* Theorem: b <= a ==> gcd (a - b) b = gcd a b *)
(* Proof:
     gcd (a - b) b
   = gcd b (a - b)         by GCD_SYM
   = gcd (b + (a - b)) b   by GCD_ADD_L
   = gcd (a - b + b) b     by ADD_COMM
   = gcd a b               by SUB_ADD, b <= a.

Note: If a < b, a - b = 0  for num, hence gcd (a - b) b = gcd 0 b = b.
*)
val GCD_SUB_L = store_thm(
  "GCD_SUB_L",
  ``!a b. b <= a ==> (gcd (a - b) b = gcd a b)``,
  metis_tac[GCD_SYM, GCD_ADD_L, ADD_COMM, SUB_ADD]);

(* Theorem: a <= b ==> gcd a (b - a) = gcd a b *)
(* Proof:
     gcd a (b - a)
   = gcd (b - a) a         by GCD_SYM
   = gcd b a               by GCD_SUB_L
   = gcd a b               by GCD_SYM
*)
val GCD_SUB_R = store_thm(
  "GCD_SUB_R",
  ``!a b. a <= b ==> (gcd a (b - a) = gcd a b)``,
  metis_tac[GCD_SYM, GCD_SUB_L]);

(* Theorem: If 1/c = 1/b - 1/a, then lcm a b = lcm a c.
            a * b = c * (a - b) ==> lcm a b = lcm a c *)
(* Proof:
   Idea:
     lcm a c
   = (a * c) DIV (gcd a c)              by lcm_def
   = (a * b * c) DIV (gcd a c) DIV b    by MULT_DIV
   = (a * b * c) DIV b * (gcd a c)      by DIV_DIV_DIV_MULT
   = (a * b * c) DIV gcd b*a b*c        by GCD_COMMON_FACTOR
   = (a * b * c) DIV gcd c*(a-b) c*b    by given
   = (a * b * c) DIV c * gcd (a-b) b    by GCD_COMMON_FACTOR
   = (a * b * c) DIV c * gcd a b        by GCD_SUB_L
   = (a * b * c) DIV c DIV gcd a b      by DIV_DIV_DIV_MULT
   = a * b DIV gcd a b                  by MULT_DIV
   = lcm a b                            by lcm_def

   Details:
   If a = 0,
      lcm 0 b = 0 = lcm 0 c          by LCM_0
   If a <> 0,
      If b = 0, a * b = 0 = c * a    by MULT_0, SUB_0
      Hence c = 0, hence true        by MULT_EQ_0
      If b <> 0, c <> 0.             by MULT_EQ_0
      So 0 < gcd a c, 0 < gcd a b    by GCD_EQ_0
      and  (gcd a c) divides a       by GCD_IS_GREATEST_COMMON_DIVISOR
      thus (gcd a c) divides (a * c) by DIVIDES_MULT
      Note (a - b) <> 0              by MULT_EQ_0
       so  ~(a <= b)                 by SUB_EQ_0
       or  b < a, or b <= a          for GCD_SUB_L later.
   Now,
      lcm a c
    = (a * c) DIV (gcd a c)                      by lcm_def
    = (b * ((a * c) DIV (gcd a c))) DIV b        by MULT_COMM, MULT_DIV
    = ((b * (a * c)) DIV (gcd a c)) DIV b        by MULTIPLY_DIV
    = (b * (a * c)) DIV ((gcd a c) * b)          by DIV_DIV_DIV_MULT
    = (b * a * c) DIV ((gcd a c) * b)            by MULT_ASSOC
    = c * (a * b) DIV (b * (gcd a c))            by MULT_COMM
    = c * (a * b) DIV (gcd (b * a) (b * c))      by GCD_COMMON_FACTOR
    = c * (a * b) DIV (gcd (a * b) (c * b))      by MULT_COMM
    = c * (a * b) DIV (gcd (c * (a-b)) (c * b))  by a * b = c * (a - b)
    = c * (a * b) DIV (c * gcd (a-b) b)          by GCD_COMMON_FACTOR
    = c * (a * b) DIV (c * gcd a b)              by GCD_SUB_L
    = c * (a * b) DIV c DIV (gcd a b)            by DIV_DIV_DIV_MULT
    = a * b DIV gcd a b                          by MULT_COMM, MULT_DIV
    = lcm a b                                    by lcm_def
*)
val LCM_EXCHANGE = store_thm(
  "LCM_EXCHANGE",
  ``!a b c. (a * b = c * (a - b)) ==> (lcm a b = lcm a c)``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  Cases_on `b = 0` >| [
    `c = 0` by metis_tac[MULT_EQ_0, SUB_0] >>
    rw[],
    `c <> 0` by metis_tac[MULT_EQ_0] >>
    `0 < b /\ 0 < c` by decide_tac >>
    `(gcd a c) divides a` by rw[GCD_IS_GREATEST_COMMON_DIVISOR] >>
    `(gcd a c) divides (a * c)` by rw[DIVIDES_MULT] >>
    `0 < gcd a c /\ 0 < gcd a b` by metis_tac[GCD_EQ_0, NOT_ZERO_LT_ZERO] >>
    `~(a <= b)` by metis_tac[SUB_EQ_0, MULT_EQ_0] >>
    `b <= a` by decide_tac >>
    `lcm a c = (a * c) DIV (gcd a c)` by rw[lcm_def] >>
    `_ = (b * ((a * c) DIV (gcd a c))) DIV b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = ((b * (a * c)) DIV (gcd a c)) DIV b` by rw[MULTIPLY_DIV] >>
    `_ = (b * (a * c)) DIV ((gcd a c) * b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = (b * a * c) DIV ((gcd a c) * b)` by rw[MULT_ASSOC] >>
    `_ = c * (a * b) DIV (b * (gcd a c))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (b * a) (b * c))` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (gcd (a * b) (c * b))` by rw_tac std_ss[MULT_COMM] >>
    `_ = c * (a * b) DIV (gcd (c * (a-b)) (c * b))` by rw[] >>
    `_ = c * (a * b) DIV (c * gcd (a-b) b)` by rw[GCD_COMMON_FACTOR] >>
    `_ = c * (a * b) DIV (c * gcd a b)` by rw[GCD_SUB_L] >>
    `_ = c * (a * b) DIV c DIV (gcd a b)` by rw[DIV_DIV_DIV_MULT] >>
    `_ = a * b DIV gcd a b` by metis_tac[MULT_COMM, MULT_DIV] >>
    `_ = lcm a b` by rw[lcm_def] >>
    decide_tac
  ]);

(* Theorem: coprime m n ==> LCM m n = m * n *)
(* Proof:
   By GCD_LCM, with gcd m n = 1.
*)
val LCM_COPRIME = store_thm(
  "LCM_COPRIME",
  ``!m n. coprime m n ==> (lcm m n = m * n)``,
  metis_tac[GCD_LCM, MULT_LEFT_1]);

(* Theorem: LCM (k * m) (k * n) = k * LCM m n *)
(* Proof:
   If m = 0 or n = 0, LHS = 0 = RHS.
   If m <> 0 and n <> 0,
     lcm (k * m) (k * n)
   = (k * m) * (k * n) / gcd (k * m) (k * n)    by GCD_LCM
   = (k * m) * (k * n) / k * (gcd m n)          by GCD_COMMON_FACTOR
   = k * m * n / (gcd m n)
   = k * LCM m n                                by GCD_LCM
*)
val LCM_COMMON_FACTOR = store_thm(
  "LCM_COMMON_FACTOR",
  ``!m n k. lcm (k * m) (k * n) = k * lcm m n``,
  rpt strip_tac >>
  `k * (k * (m * n)) = (k * m) * (k * n)` by rw_tac arith_ss[] >>
  `_ = gcd (k * m) (k * n) * lcm (k * m) (k * n) ` by rw[GCD_LCM] >>
  `_ = k * (gcd m n) * lcm (k * m) (k * n)` by rw[GCD_COMMON_FACTOR] >>
  `_ = k * ((gcd m n) * lcm (k * m) (k * n))` by rw_tac arith_ss[] >>
  Cases_on `k = 0` >-
  rw[] >>
  `(gcd m n) * lcm (k * m) (k * n) = k * (m * n)` by metis_tac[MULT_LEFT_CANCEL] >>
  `_ = k * ((gcd m n) * (lcm m n))` by rw_tac std_ss[GCD_LCM] >>
  `_ = (gcd m n) * (k * (lcm m n))` by rw_tac arith_ss[] >>
  Cases_on `n = 0` >-
  rw[] >>
  metis_tac[MULT_LEFT_CANCEL, GCD_EQ_0]);

(* Theorem: coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c *)
(* Proof:
     lcm (a * c) (b * c)
   = lcm (c * a) (c * b)     by MULT_COMM
   = c * (lcm a b)           by LCM_COMMON_FACTOR
   = (lcm a b) * c           by MULT_COMM
   = a * b * c               by LCM_COPRIME
*)
val LCM_COMMON_COPRIME = store_thm(
  "LCM_COMMON_COPRIME",
  ``!a b. coprime a b ==> !c. lcm (a * c) (b * c) = a * b * c``,
  metis_tac[LCM_COMMON_FACTOR, LCM_COPRIME, MULT_COMM]);

(* Theorem: 0 < n /\ m MOD n = 0 ==> gcd m n = n *)
(* Proof:
   Since m MOD n = 0
         ==> n divides m     by DIVIDES_MOD_0
   Hence gcd m n = gcd n m   by GCD_SYM
                 = n         by divides_iff_gcd_fix
*)
val GCD_MULTIPLE = store_thm(
  "GCD_MULTIPLE",
  ``!m n. 0 < n /\ (m MOD n = 0) ==> (gcd m n = n)``,
  metis_tac[DIVIDES_MOD_0, divides_iff_gcd_fix, GCD_SYM]);

(* Theorem: gcd (m * n) n = n *)
(* Proof:
     gcd (m * n) n
   = gcd (n * m) n          by MULT_COMM
   = gcd (n * m) (n * 1)    by MULT_RIGHT_1
   = n * (gcd m 1)          by GCD_COMMON_FACTOR
   = n * 1                  by GCD_1
   = n                      by MULT_RIGHT_1
*)
val GCD_MULTIPLE_ALT = store_thm(
  "GCD_MULTIPLE_ALT",
  ``!m n. gcd (m * n) n = n``,
  rpt strip_tac >>
  `gcd (m * n) n = gcd (n * m) n` by rw[MULT_COMM] >>
  `_ = gcd (n * m) (n * 1)` by rw[] >>
  rw[GCD_COMMON_FACTOR]);

(* Theorem: k * a <= b ==> gcd a b = gcd a (b - k * a) *)
(* Proof:
   By induction on k.
   Base case: 0 * a <= b ==> gcd a b = gcd a (b - 0 * a)
     True since b - 0 * a = b       by MULT, SUB_0
   Step case: k * a <= b ==> (gcd a b = gcd a (b - k * a)) ==>
              SUC k * a <= b ==> (gcd a b = gcd a (b - SUC k * a))
         SUC k * a <= b
     ==> k * a + a <= b             by MULT
        so       a <= b - k * a     by arithmetic [1]
       and   k * a <= b             by 0 <= b - k * a, [2]
       gcd a (b - SUC k * a)
     = gcd a (b - (k * a + a))      by MULT
     = gcd a (b - k * a - a)        by arithmetic
     = gcd a (b - k * a - a + a)    by GCD_ADD_L, ADD_COMM
     = gcd a (b - k * a)            by SUB_ADD, a <= b - k * a [1]
     = gcd a b                      by induction hypothesis, k * a <= b [2]
*)
val GCD_SUB_MULTIPLE = store_thm(
  "GCD_SUB_MULTIPLE",
  ``!a b k. k * a <= b ==> (gcd a b = gcd a (b - k * a))``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[] >>
  rw_tac std_ss[] >>
  `k * a + a <= b` by metis_tac[MULT] >>
  `a <= b - k * a` by decide_tac >>
  `k * a <= b` by decide_tac >>
  `gcd a (b - SUC k * a) = gcd a (b - (k * a + a))` by rw[MULT] >>
  `_ = gcd a (b - k * a - a)` by rw_tac arith_ss[] >>
  `_ = gcd a (b - k * a - a + a)` by rw[GCD_ADD_L, ADD_COMM] >>
  rw_tac std_ss[SUB_ADD]);

(* Theorem: k * a <= b ==> (gcd b a = gcd a (b - k * a)) *)
(* Proof: by GCD_SUB_MULTIPLE, GCD_SYM *)
val GCD_SUB_MULTIPLE_COMM = store_thm(
  "GCD_SUB_MULTIPLE_COMM",
  ``!a b k. k * a <= b ==> (gcd b a = gcd a (b - k * a))``,
  metis_tac[GCD_SUB_MULTIPLE, GCD_SYM]);

(* Theorem: 0 < m ==> (gcd m n = gcd m (n MOD m)) *)
(* Proof:
     gcd m n
   = gcd (n MOD m) m       by GCD_EFFICIENTLY, m <> 0
   = gcd m (n MOD m)       by GCD_SYM
*)
val GCD_MOD = store_thm(
  "GCD_MOD",
  ``!m n. 0 < m ==> (gcd m n = gcd m (n MOD m))``,
  rw[Once GCD_EFFICIENTLY, GCD_SYM]);

(* Theorem: 0 < m ==> (gcd n m = gcd (n MOD m) m) *)
(* Proof: by GCD_MOD, GCD_COMM *)
val GCD_MOD_COMM = store_thm(
  "GCD_MOD_COMM",
  ``!m n. 0 < m ==> (gcd n m = gcd (n MOD m) m)``,
  metis_tac[GCD_MOD, GCD_COMM]);

(* Theorem: gcd a (b * a + c) = gcd a c *)
(* Proof:
   If a = 0,
      Then b * 0 + c = c             by arithmetic
      Hence trivially true.
   If a <> 0,
      gcd a (b * a + c)
    = gcd ((b * a + c) MOD a) a      by GCD_EFFICIENTLY, 0 < a
    = gcd (c MOD a) a                by MOD_TIMES, 0 < a
    = gcd a c                        by GCD_EFFICIENTLY, 0 < a
*)
val GCD_EUCLID = store_thm(
  "GCD_EUCLID",
  ``!a b c. gcd a (b * a + c) = gcd a c``,
  rpt strip_tac >>
  Cases_on `a = 0` >-
  rw[] >>
  metis_tac[GCD_EFFICIENTLY, MOD_TIMES, NOT_ZERO_LT_ZERO]);

(* Theorem: gcd (b * a + c) a = gcd a c *)
(* Proof: by GCD_EUCLID, GCD_SYM *)
val GCD_REDUCE = store_thm(
  "GCD_REDUCE",
  ``!a b c. gcd (b * a + c) a = gcd a c``,
  rw[GCD_EUCLID, GCD_SYM]);

(* Theorem alias *)
Theorem GCD_REDUCE_BY_COPRIME = GCD_CANCEL_MULT;
(* val GCD_REDUCE_BY_COPRIME =
   |- !m n k. coprime m k ==> gcd m (k * n) = gcd m n: thm *)

(* Idea: a crude upper bound for greatest common divisor.
         A better upper bound is: gcd m n <= MIN m n, by MIN_LE *)

(* Theorem: 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n *)
(* Proof:
   Let g = gcd m n.
   Then g divides m /\ g divides n   by GCD_PROPERTY
     so g <= m /\ g <= n             by DIVIDES_LE,  0 < m, 0 < n
*)
Theorem gcd_le:
  !m n. 0 < m /\ 0 < n ==> gcd m n <= m /\ gcd m n <= n
Proof
  ntac 3 strip_tac >>
  qabbrev_tac `g = gcd m n` >>
  `g divides m /\ g divides n` by metis_tac[GCD_PROPERTY] >>
  simp[DIVIDES_LE]
QED

(* Idea: a generalisation of GCD_LINEAR:
|- !j k. 0 < j ==> ?p q. p * j = q * k + gcd j k
   This imposes a condition for (gcd a b) divides c.
*)

(* Theorem: 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c) *)
(* Proof:
   Let d = gcd a b.
   If part: d divides c ==> ?p q. p * a = q * b + c
      Note ?k. c = k * d                 by divides_def
       and ?u v. u * a = v * b + d       by GCD_LINEAR, 0 < a
        so (k * u) * a = (k * v) * b + (k * d)
      Take p = k * u, q = k * v,
      Then p * q = q * b + c
   Only-if part: p * a = q * b + c ==> d divides c
      Note d divides a /\ d divides b    by GCD_PROPERTY
        so d divides c                   by divides_linear_sub
*)
Theorem gcd_divides_iff:
  !a b c. 0 < a ==> ((gcd a b) divides c <=> ?p q. p * a = q * b + c)
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  rw_tac bool_ss[EQ_IMP_THM] >| [
    `?k. c = k * d` by rw[GSYM divides_def] >>
    `?p q. p * a = q * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
    `k * (p * a) = k * (q * b + d)` by fs[] >>
    `_ = k * (q * b) + k * d` by decide_tac >>
    metis_tac[MULT_ASSOC],
    `d divides a /\ d divides b` by metis_tac[GCD_PROPERTY] >>
    metis_tac[divides_linear_sub]
  ]
QED

(* Theorem alias *)
Theorem gcd_linear_thm = gcd_divides_iff;
(* val gcd_linear_thm =
|- !a b c. 0 < a ==> (gcd a b divides c <=> ?p q. p * a = q * b + c): thm *)

(* Idea: a version of GCD_LINEAR for MOD, without negatives.
   That is: in MOD n. gcd (a b) can be expressed as a linear combination of a b. *)

(* Theorem: 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n *)
(* Proof:
   Let d = gcd a b.
   Then ?h k. h * a = k * b + d                by GCD_LINEAR, 0 < a
   Let p = h, q = k * n - k.
   Then q + k = k * n.
          (p * a) MOD n = (k * b + d) MOD n
   <=>    (p * a + q * b) MOD n = (q * b + k * b + d) MOD n    by ADD_MOD
   <=>    (p * a + q * b) MOD n = (k * b * n + d) MOD n        by above
   <=>    (p * a + q * b) MOD n = d MOD n                      by MOD_TIMES
*)
Theorem gcd_linear_mod_thm:
  !n a b. 0 < n /\ 0 < a ==> ?p q. (p * a + q * b) MOD n = gcd a b MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?p k. p * a = k * b + d` by rw[GCD_LINEAR, Abbr`d`] >>
  `k <= k * n` by fs[] >>
  `k * n - k + k = k * n` by decide_tac >>
  qabbrev_tac `q = k * n - k` >>
  qexists_tac `p` >>
  qexists_tac `q` >>
  `(p * a + q * b) MOD n = (q * b + k * b + d) MOD n` by rw[ADD_MOD] >>
  `_ = ((q + k) * b + d) MOD n` by decide_tac >>
  `_ = (k * b * n + d) MOD n` by rfs[] >>
  simp[MOD_TIMES]
QED

(* Idea: a simplification of gcd_linear_mod_thm when n = a. *)

(* Theorem: 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a *)
(* Proof:
   Let g = gcd a b.
   Then ?p q. (p * a + q * b) MOD a = g MOD a  by gcd_linear_mod_thm, n = a
     so               (q * b) MOD a = g MOD a  by MOD_TIMES
*)
Theorem gcd_linear_mod_1:
  !a b. 0 < a ==> ?q. (q * b) MOD a = (gcd a b) MOD a
Proof
  metis_tac[gcd_linear_mod_thm, MOD_TIMES]
QED

(* Idea: symmetric version of of gcd_linear_mod_1. *)

(* Theorem: 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b *)
(* Proof:
   Note ?p. (p * a) MOD b = (gcd b a) MOD b    by gcd_linear_mod_1
     or                   = (gcd a b) MOD b    by GCD_SYM
*)
Theorem gcd_linear_mod_2:
  !a b. 0 < b ==> ?p. (p * a) MOD b = (gcd a b) MOD b
Proof
  metis_tac[gcd_linear_mod_1, GCD_SYM]
QED

(* Idea: replacing n = a * b in gcd_linear_mod_thm. *)

(* Theorem: 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b) *)
(* Proof: by gcd_linear_mod_thm, n = a * b. *)
Theorem gcd_linear_mod_prod:
  !a b. 0 < a /\ 0 < b ==> ?p q. (p * a + q * b) MOD (a * b) = (gcd a b) MOD (a * b)
Proof
  simp[gcd_linear_mod_thm]
QED

(* Idea: specialise gcd_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b) *)
(* Proof: by gcd_linear_mod_prod. *)
Theorem coprime_linear_mod_prod:
  !a b. 0 < a /\ 0 < b /\ coprime a b ==>
  ?p q. (p * a + q * b) MOD (a * b) = 1 MOD (a * b)
Proof
  metis_tac[gcd_linear_mod_prod]
QED

(* Idea: generalise gcd_linear_mod_thm for multiple of gcd a b. *)

(* Theorem: 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n *)
(* Proof:
   Let d = gcd a b.
   Note k. c = k * d                           by divides_def
    and ?p q. (p * a + q * b) MOD n = d MOD n  by gcd_linear_mod_thm
   Thus (k * d) MOD n
      = (k * (p * a + q * b)) MOD n            by MOD_TIMES2, 0 < n
      = (k * p * a + k * q * b) MOD n          by LEFT_ADD_DISTRIB
   Take (k * p) and (k * q) for the eventual p and q.
*)
Theorem gcd_multiple_linear_mod_thm:
  !n a b c. 0 < n /\ 0 < a /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD n = c MOD n
Proof
  rpt strip_tac >>
  qabbrev_tac `d = gcd a b` >>
  `?k. c = k * d` by rw[GSYM divides_def] >>
  `?p q. (p * a + q * b) MOD n = d MOD n` by metis_tac[gcd_linear_mod_thm] >>
  `(k * (p * a + q * b)) MOD n = (k * d) MOD n` by metis_tac[MOD_TIMES2] >>
  `k * (p * a + q * b) = k * p * a + k * q * b` by decide_tac >>
  metis_tac[]
QED

(* Idea: specialise gcd_multiple_linear_mod_thm for n = a * b. *)

(* Theorem: 0 < a /\ 0 < b /\ gcd a b divides c ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)) *)
(* Proof: by gcd_multiple_linear_mod_thm. *)
Theorem gcd_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ gcd a b divides c ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  simp[gcd_multiple_linear_mod_thm]
QED

(* Idea: specialise gcd_multiple_linear_mod_prod for coprime a b. *)

(* Theorem: 0 < a /\ 0 < b /\ coprime a b ==>
            ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b) *)
(* Proof:
   Note coprime a b means gcd a b = 1    by notation
    and 1 divides c                      by ONE_DIVIDES_ALL
     so the result follows               by gcd_multiple_linear_mod_prod
*)
Theorem coprime_multiple_linear_mod_prod:
  !a b c. 0 < a /\ 0 < b /\ coprime a b ==>
          ?p q. (p * a + q * b) MOD (a * b) = c MOD (a * b)
Proof
  metis_tac[gcd_multiple_linear_mod_prod, ONE_DIVIDES_ALL]
QED

(* ------------------------------------------------------------------------- *)
(* Coprime Theorems                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: coprime n (n + 1) *)
(* Proof:
   Since n < n + 1 ==> n <= n + 1,
     gcd n (n + 1)
   = gcd n (n + 1 - n)      by GCD_SUB_R
   = gcd n 1                by arithmetic
   = 1                      by GCD_1
*)
val coprime_SUC = store_thm(
  "coprime_SUC",
  ``!n. coprime n (n + 1)``,
  rw[GCD_SUB_R]);

(* Theorem: 0 < n ==> coprime n (n - 1) *)
(* Proof:
     gcd n (n - 1)
   = gcd (n - 1) n             by GCD_SYM
   = gcd (n - 1) (n - 1 + 1)   by SUB_ADD, 0 <= n
   = 1                         by coprime_SUC
*)
val coprime_PRE = store_thm(
  "coprime_PRE",
  ``!n. 0 < n ==> coprime n (n - 1)``,
  metis_tac[GCD_SYM, coprime_SUC, DECIDE``!n. 0 < n ==> (n - 1 + 1 = n)``]);

(* Theorem: coprime 0 n ==> n = 1 *)
(* Proof:
   gcd 0 n = n    by GCD_0L
           = 1    by coprime 0 n
*)
val coprime_0L = store_thm(
  "coprime_0L",
  ``!n. coprime 0 n <=> (n = 1)``,
  rw[GCD_0L]);

(* Theorem: coprime n 0 ==> n = 1 *)
(* Proof:
   gcd n 0 = n    by GCD_0L
           = 1    by coprime n 0
*)
val coprime_0R = store_thm(
  "coprime_0R",
  ``!n. coprime n 0 <=> (n = 1)``,
  rw[GCD_0R]);

(* Theorem: (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1) *)
(* Proof: by coprime_0L, coprime_0R *)
Theorem coprime_0:
  !n. (coprime 0 n <=> n = 1) /\ (coprime n 0 <=> n = 1)
Proof
  simp[coprime_0L, coprime_0R]
QED

(* Theorem: coprime x y = coprime y x *)
(* Proof:
         coprime x y
   means gcd x y = 1
      so gcd y x = 1   by GCD_SYM
    thus coprime y x
*)
val coprime_sym = store_thm(
  "coprime_sym",
  ``!x y. coprime x y = coprime y x``,
  rw[GCD_SYM]);

(* Theorem: coprime k n /\ n <> 1 ==> k <> 0 *)
(* Proof: by coprime_0L *)
val coprime_neq_1 = store_thm(
  "coprime_neq_1",
  ``!n k. coprime k n /\ n <> 1 ==> k <> 0``,
  fs[coprime_0L]);

(* Theorem: coprime k n /\ 1 < n ==> 0 < k *)
(* Proof: by coprime_neq_1 *)
val coprime_gt_1 = store_thm(
  "coprime_gt_1",
  ``!n k. coprime k n /\ 1 < n ==> 0 < k``,
  metis_tac[coprime_neq_1, NOT_ZERO_LT_ZERO, DECIDE``~(1 < 1)``]);

(* Note:  gcd (c ** n) m = gcd c m  is false when n = 0, where c ** 0 = 1. *)

(* Theorem: coprime c m ==> !n. coprime (c ** n) m *)
(* Proof: by induction on n.
   Base case: coprime (c ** 0) m
     Since c ** 0 = 1         by EXP
     and coprime 1 m is true  by GCD_1
   Step case: coprime c m /\ coprime (c ** n) m ==> coprime (c ** SUC n) m
     coprime c m means
     coprime m c              by GCD_SYM

       gcd m (c ** SUC n)
     = gcd m (c * c ** n)     by EXP
     = gcd m (c ** n)         by GCD_CANCEL_MULT, coprime m c
     = 1                      by induction hypothesis
     Hence coprime m (c ** SUC n)
     or coprime (c ** SUC n) m  by GCD_SYM
*)
val coprime_exp = store_thm(
  "coprime_exp",
  ``!c m. coprime c m ==> !n. coprime (c ** n) m``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP, GCD_1] >>
  metis_tac[EXP, GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime a b ==> !n. coprime a (b ** n) *)
(* Proof: by coprime_exp, GCD_SYM *)
val coprime_exp_comm = store_thm(
  "coprime_exp_comm",
  ``!a b. coprime a b ==> !n. coprime a (b ** n)``,
  metis_tac[coprime_exp, GCD_SYM]);

(* Theorem: 0 < n ==> !a b. coprime a b <=> coprime a (b ** n) *)
(* Proof:
   If part: coprime a b ==> coprime a (b ** n)
      True by coprime_exp_comm.
   Only-if part: coprime a (b ** n) ==> coprime a b
      If a = 0,
         then b ** n = 1        by GCD_0L
          and b = 1             by EXP_EQ_1, n <> 0
         Hence coprime 0 1      by GCD_0L
      If a <> 0,
      Since coprime a (b ** n) means
            ?h k. h * a = k * b ** n + 1   by LINEAR_GCD, GCD_SYM
   Let d = gcd a b.
   Since d divides a and d divides b       by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides b ** n                  by divides_exp, 0 < n
      so d divides 1                       by divides_linear_sub
    Thus d = 1                             by DIVIDES_ONE
      or coprime a b                       by notation
*)
val coprime_iff_coprime_exp = store_thm(
  "coprime_iff_coprime_exp",
  ``!n. 0 < n ==> !a b. coprime a b <=> coprime a (b ** n)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_exp_comm] >>
  `n <> 0` by decide_tac >>
  Cases_on `a = 0` >-
  metis_tac[GCD_0L, EXP_EQ_1] >>
  `?h k. h * a = k * b ** n + 1` by metis_tac[LINEAR_GCD, GCD_SYM] >>
  qabbrev_tac `d = gcd a b` >>
  `d divides a /\ d divides b` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides (b ** n)` by rw[divides_exp] >>
  `d divides 1` by metis_tac[divides_linear_sub] >>
  rw[GSYM DIVIDES_ONE]);

(* Theorem: coprime x z /\ coprime y z ==> coprime (x * y) z *)
(* Proof:
   By GCD_CANCEL_MULT:
   |- !m n k. coprime m k ==> (gcd m (k * n) = gcd m n)
   Hence follows by coprime_sym.
*)
val coprime_product_coprime = store_thm(
  "coprime_product_coprime",
  ``!x y z. coprime x z /\ coprime y z ==> coprime (x * y) z``,
  metis_tac[GCD_CANCEL_MULT, GCD_SYM]);

(* Theorem: coprime z x /\ coprime z y ==> coprime z (x * y) *)
(* Proof:
   Note gcd z x = 1         by given
    ==> gcd z (x * y)
      = gcd z y             by GCD_CANCEL_MULT
      = 1                   by given
*)
val coprime_product_coprime_sym = store_thm(
  "coprime_product_coprime_sym",
  ``!x y z. coprime z x /\ coprime z y ==> coprime z (x * y)``,
  rw[GCD_CANCEL_MULT]);
(* This is the same as PRODUCT_WITH_GCD_ONE *)

(* Theorem: coprime x z ==> (coprime y z <=> coprime (x * y) z) *)
(* Proof:
   If part: coprime x z /\ coprime y z ==> coprime (x * y) z
      True by coprime_product_coprime
   Only-if part: coprime x z /\ coprime (x * y) z ==> coprime y z
      Let d = gcd y z.
      Then d divides z /\ d divides y     by GCD_PROPERTY
        so d divides (x * y)              by DIVIDES_MULT, MULT_COMM
        or d divides (gcd (x * y) z)      by GCD_PROPERTY
           d divides 1                    by coprime (x * y) z
       ==> d = 1                          by DIVIDES_ONE
        or coprime y z                    by notation
*)
val coprime_product_coprime_iff = store_thm(
  "coprime_product_coprime_iff",
  ``!x y z. coprime x z ==> (coprime y z <=> coprime (x * y) z)``,
  rw[EQ_IMP_THM] >-
  rw[coprime_product_coprime] >>
  qabbrev_tac `d = gcd y z` >>
  metis_tac[GCD_PROPERTY, DIVIDES_MULT, MULT_COMM, DIVIDES_ONE]);

(* Theorem: a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n *)
(* Proof: by LCM_COPRIME, LCM_DIVIDES *)
val coprime_product_divides = store_thm(
  "coprime_product_divides",
  ``!n a b. a divides n /\ b divides n /\ coprime a b ==> (a * b) divides n``,
  metis_tac[LCM_COPRIME, LCM_DIVIDES]);

(* Theorem: 0 < m /\ coprime m n ==> coprime m (n MOD m) *)
(* Proof:
     gcd m n
   = if m = 0 then n else gcd (n MOD m) m    by GCD_EFFICIENTLY
   = gcd (n MOD m) m                         by decide_tac, m <> 0
   = gcd m (n MOD m)                         by GCD_SYM
   Hence true since coprime m n <=> gcd m n = 1.
*)
val coprime_mod = store_thm(
  "coprime_mod",
  ``!m n. 0 < m /\ coprime m n ==> coprime m (n MOD m)``,
  metis_tac[GCD_EFFICIENTLY, GCD_SYM, NOT_ZERO_LT_ZERO]);

(* Theorem: 0 < m ==> (coprime m n = coprime m (n MOD m)) *)
(* Proof: by GCD_MOD *)
val coprime_mod_iff = store_thm(
  "coprime_mod_iff",
  ``!m n. 0 < m ==> (coprime m n = coprime m (n MOD m))``,
  rw[Once GCD_MOD]);

(* Theorem: 1 < n /\ coprime n m ==> ~(n divides m) *)
(* Proof:
       coprime n m
   ==> gcd n m = 1       by notation
   ==> n MOD m <> 0      by MOD_NONZERO_WHEN_GCD_ONE, with 1 < n
   ==> ~(n divides m)    by DIVIDES_MOD_0, with 0 < n
*)
val coprime_not_divides = store_thm(
  "coprime_not_divides",
  ``!m n. 1 < n /\ coprime n m ==> ~(n divides m)``,
  metis_tac[MOD_NONZERO_WHEN_GCD_ONE, DIVIDES_MOD_0, ONE_LT_POS, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 < n /\ coprime n k /\ 1 < p /\ p divides n ==> ~(p divides k) *)
(* Proof:
   First, 1 < n ==> n <> 0 and n <> 1
   If k = 0, gcd n k = n        by GCD_0R
   But coprime n k means gcd n k = 1, so k <> 0.
   By contradiction.
   If p divides k, and given p divides n,
   then p divides gcd n k = 1   by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0 and k <> 0
   or   p = 1                   by DIVIDES_ONE
   which contradicts 1 < p.
*)
val coprime_factor_not_divides = store_thm(
  "coprime_factor_not_divides",
  ``!n k. 1 < n /\ coprime n k ==> !p. 1 < p /\ p divides n ==> ~(p divides k)``,
  rpt strip_tac >>
  `n <> 0 /\ n <> 1 /\ p <> 1` by decide_tac >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_ONE, GCD_0R]);

(* Theorem: m divides n ==> !k. coprime n k ==> coprime m k *)
(* Proof:
   Let d = gcd m k.
   Then d divides m /\ d divides k    by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d divides n                   by DIVIDES_TRANS
     so d divides 1                   by GCD_IS_GREATEST_COMMON_DIVISOR, coprime n k
    ==> d = 1                         by DIVIDES_ONE
*)
val coprime_factor_coprime = store_thm(
  "coprime_factor_coprime",
  ``!m n. m divides n ==> !k. coprime n k ==> coprime m k``,
  rpt strip_tac >>
  qabbrev_tac `d = gcd m k` >>
  `d divides m /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides n` by metis_tac[DIVIDES_TRANS] >>
  `d divides 1` by metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR] >>
  rw[GSYM DIVIDES_ONE]);

(* Idea: common factor of two coprime numbers. *)

(* Theorem: coprime a b /\ c divides a /\ c divides b ==> c = 1 *)
(* Proof:
   Note c divides gcd a b      by GCD_PROPERTY
     or c divides 1            by coprime a b
     so c = 1                  by DIVIDES_ONE
*)
Theorem coprime_common_factor:
  !a b c. coprime a b /\ c divides a /\ c divides b ==> c = 1
Proof
  metis_tac[GCD_PROPERTY, DIVIDES_ONE]
QED


(* Theorem: prime p /\ ~(p divides n) ==> coprime p n *)
(* Proof:
   Since divides p 0, so n <> 0.    by ALL_DIVIDES_0
   If n = 1, certainly coprime p n  by GCD_1
   If n <> 1,
   Let gcd p n = d.
   Since d divides p                by GCD_IS_GREATEST_COMMON_DIVISOR
     and prime p                    by given
      so d = 1 or d = p             by prime_def
     but d <> p                     by divides_iff_gcd_fix
   Hence d = 1, or coprime p n.
*)
val prime_not_divides_coprime = store_thm(
  "prime_not_divides_coprime",
  ``!n p. prime p /\ ~(p divides n) ==> coprime p n``,
  rpt strip_tac >>
  `n <> 0` by metis_tac[ALL_DIVIDES_0] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < p` by rw[PRIME_POS] >>
  `p <> 0` by decide_tac >>
  metis_tac[prime_def, divides_iff_gcd_fix, GCD_IS_GREATEST_COMMON_DIVISOR]);

(* Theorem: prime p /\ ~(coprime p n) ==> p divides n *)
(* Proof:
   Let d = gcd p n.
   Then d divides p        by GCD_IS_GREATEST_COMMON_DIVISOR
    ==> d = p              by prime_def
   Thus p divides n        by divides_iff_gcd_fix

   Or: this is just the inverse of prime_not_divides_coprime.
*)
val prime_not_coprime_divides = store_thm(
  "prime_not_coprime_divides",
  ``!n p. prime p /\ ~(coprime p n) ==> p divides n``,
  metis_tac[prime_not_divides_coprime]);

(* Theorem: 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k *)
(* Proof:
   Since coprime n k /\ p divides n
     ==> ~(p divides k)               by coprime_factor_not_divides
    Then prime p /\ ~(p divides k)
     ==> coprime p k                  by prime_not_divides_coprime
*)
val coprime_prime_factor_coprime = store_thm(
  "coprime_prime_factor_coprime",
  ``!n p. 1 < n /\ prime p /\ p divides n ==> !k. coprime n k ==> coprime p k``,
  metis_tac[coprime_factor_not_divides, prime_not_divides_coprime, ONE_LT_PRIME]);

(* This is better:
coprime_factor_coprime
|- !m n. m divides n ==> !k. coprime n k ==> coprime m k
*)

(* Theorem: 1 < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n *)
(* Proof:
   By contradiction. Suppose n <= m.
   Since 1 < n means 0 < n and n <> 1,
   The implication shows
       coprime n n, or n = 1   by notation
   But gcd n n = n             by GCD_REF
   This contradicts n <> 1.
*)
val coprime_all_le_imp_lt = store_thm(
  "coprime_all_le_imp_lt",
  ``!n. 1 < n ==> !m. (!j. 0 < j /\ j <= m ==> coprime n j) ==> m < n``,
  spose_not_then strip_assume_tac >>
  `n <= m` by decide_tac >>
  `0 < n /\ n <> 1` by decide_tac >>
  metis_tac[GCD_REF]);

(* Theorem: (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n) *)
(* Proof:
   If part: (!j. 1 < j /\ j <= m ==> ~(j divides n)) /\ 1 < j /\ j <= m ==> coprime j n
      Let d = gcd j n.
      Then d divides j /\ d divides n         by GCD_IS_GREATEST_COMMON_DIVISOR
       Now 1 < j ==> 0 < j /\ j <> 0
        so d <= j                             by DIVIDES_LE, 0 < j
       and d <> 0                             by GCD_EQ_0, j <> 0
      By contradiction, suppose d <> 1.
      Then 1 < d /\ d <= m                    by d <> 1, d <= j /\ j <= m
        so ~(d divides n), a contradiction    by implication

   Only-if part: (!j. 1 < j /\ j <= m ==> coprime j n) /\ 1 < j /\ j <= m ==> ~(j divides n)
      Since coprime j n                       by implication
         so ~(j divides n)                    by coprime_not_divides
*)
val coprime_condition = store_thm(
  "coprime_condition",
  ``!m n. (!j. 1 < j /\ j <= m ==> ~(j divides n)) <=> (!j. 1 < j /\ j <= m ==> coprime j n)``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `d = gcd j n` >>
    `d divides j /\ d divides n` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
    `0 < j /\ j <> 0` by decide_tac >>
    `d <= j` by rw[DIVIDES_LE] >>
    `d <> 0` by metis_tac[GCD_EQ_0] >>
    `1 < d /\ d <= m` by decide_tac >>
    metis_tac[],
    metis_tac[coprime_not_divides]
  ]);

(* Note:
The above is the generalization of this observation:
- a prime n  has all 1 < j < n coprime to n. Therefore,
- a number n has all 1 < j < m coprime to n, where m is the first non-trivial factor of n.
  Of course, the first non-trivial factor of n must be a prime.
*)

(* Theorem: 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n *)
(* Proof: by coprime_condition, taking j = m. *)
val coprime_by_le_not_divides = store_thm(
  "coprime_by_le_not_divides",
  ``!m n. 1 < m /\ (!j. 1 < j /\ j <= m ==> ~(j divides n)) ==> coprime m n``,
  rw[coprime_condition]);

(* Idea: a characterisation of the coprime property of two numbers. *)

(* Theorem: coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n) *)
(* Proof:
   If part: coprime m n /\ prime p ==> ~(p divides m) \/ ~(p divides n)
      By contradiction, suppose p divides m /\ p divides n.
      Then p = 1                   by coprime_common_factor
      This contradicts prime p     by NOT_PRIME_1
   Only-if part: !p. prime p ==> ~(p divides m) \/ ~(p divides m) ==> coprime m n
      Let d = gcd m n.
      By contradiction, suppose d <> 1.
      Then ?p. prime p /\ p divides d    by PRIME_FACTOR, d <> 1.
       Now d divides m /\ d divides n    by GCD_PROPERTY
        so p divides m /\ p divides n    by DIVIDES_TRANS
      This contradicts the assumption.
*)
Theorem coprime_by_prime_factor:
  !m n. coprime m n <=> !p. prime p ==> ~(p divides m /\ p divides n)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[coprime_common_factor, NOT_PRIME_1] >>
  qabbrev_tac `d = gcd m n` >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides d` by rw[PRIME_FACTOR] >>
  `d divides m /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  metis_tac[DIVIDES_TRANS]
QED

(* Idea: coprime_by_prime_factor with reduced testing of primes, useful in practice. *)

(* Theorem: 0 < m /\ 0 < n ==>
           (coprime m n <=>
           !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n)) *)
(* Proof:
   If part: coprime m n /\ prime p /\ ... ==> ~(p divides m) \/ ~(p divides n)
      By contradiction, suppose p divides m /\ p divides n.
      Then p = 1                   by coprime_common_factor
      This contradicts prime p     by NOT_PRIME_1
   Only-if part: !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m) \/ ~(p divides m) ==> coprime m n
      Let d = gcd m n.
      By contradiction, suppose d <> 1.
      Then ?p. prime p /\ p divides d    by PRIME_FACTOR, d <> 1.
       Now d divides m /\ d divides n    by GCD_PROPERTY
        so p divides m /\ p divides n    by DIVIDES_TRANS
      Thus p <= m /\ p <= n              by DIVIDES_LE, 0 < m, 0 < n
      This contradicts the assumption.
*)
Theorem coprime_by_prime_factor_le:
  !m n. 0 < m /\ 0 < n ==>
        (coprime m n <=>
        !p. prime p /\ p <= m /\ p <= n ==> ~(p divides m /\ p divides n))
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[coprime_common_factor, NOT_PRIME_1] >>
  qabbrev_tac `d = gcd m n` >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p divides d` by rw[PRIME_FACTOR] >>
  `d divides m /\ d divides n` by metis_tac[GCD_PROPERTY] >>
  `0 < p` by rw[PRIME_POS] >>
  metis_tac[DIVIDES_TRANS, DIVIDES_LE]
QED

(* Idea: establish coprime (p * a + q * b) (a * b). *)
(* Note: the key is to apply coprime_by_prime_factor. *)

(* Theorem: coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b) *)
(* Proof:
   Let z = p * a + q * b, c = a * b, d = gcd z c.
   Then d divides z /\ d divides c       by GCD_PROPERTY
   By coprime_by_prime_factor, we need to show:
      !t. prime t ==> ~(t divides z /\ t divides c)
   By contradiction, suppose t divides z /\ t divides c.
   Then t divides d                      by GCD_PROPERTY
     or t divides c where c = a * b      by DIVIDES_TRANS
     so t divides a or p divides b       by P_EUCLIDES

   If t divides a,
      Then t divides (q * b)             by divides_linear_sub
       and ~(t divides b)                by coprime_common_factor, NOT_PRIME_1
        so t divides q                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   If t divides b,
      Then t divides (p * a)             by divides_linear_sub
       and ~(t divides a)                by coprime_common_factor, NOT_PRIME_1
        so t divides p                   by P_EUCLIDES
       ==> t = 1                         by coprime_common_factor
       This contradicts prime t          by NOT_PRIME_1
   Since all lead to contradiction, we have shown:
     !t. prime t ==> ~(t divides z /\ t divides c)
   Thus coprime z c                      by coprime_by_prime_factor
*)
Theorem coprime_linear_mult:
  !a b p q. coprime a b /\ coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
Proof
  rpt strip_tac >>
  qabbrev_tac `z = p * a + q * b` >>
  qabbrev_tac `c = a * b` >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides a \/ p' divides b` by metis_tac[P_EUCLIDES] >| [
    `p' divides (q * b)` by metis_tac[divides_linear_sub, MULT_LEFT_1] >>
    `~(p' divides b)` by metis_tac[coprime_common_factor, NOT_PRIME_1] >>
    `p' divides q` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1],
    `p' divides (p * a)` by metis_tac[divides_linear_sub, MULT_LEFT_1, ADD_COMM] >>
    `~(p' divides a)` by metis_tac[coprime_common_factor, NOT_PRIME_1, MULT_COMM] >>
    `p' divides p` by metis_tac[P_EUCLIDES] >>
    metis_tac[coprime_common_factor, NOT_PRIME_1]
  ]
QED

(* Idea: include converse of coprime_linear_mult. *)

(* Theorem: coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b)) *)
(* Proof:
   If part: coprime p b /\ coprime q a ==> coprime (p * a + q * b) (a * b)
      This is true by coprime_linear_mult.
   Only-if: coprime (p * a + q * b) (a * b) ==> coprime p b /\ coprime q a
      Let z = p * a + q * b. Consider a prime t.
      For coprime p b.
          If t divides p /\ t divides b,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime p b         by coprime_by_prime_factor
      For coprime q a.
          If t divides q /\ t divides a,
          Then t divides z         by divides_linear
           and t divides (a * b)   by DIVIDES_MULTIPLE
            so t = 1               by coprime_common_factor
          This contradicts prime t by NOT_PRIME_1
          Thus coprime q a         by coprime_by_prime_factor
*)
Theorem coprime_linear_mult_iff:
  !a b p q. coprime a b ==>
            ((coprime p b /\ coprime q a) <=> coprime (p * a + q * b) (a * b))
Proof
  rw_tac std_ss[EQ_IMP_THM] >-
  simp[coprime_linear_mult] >-
 (irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by rw[DIVIDES_MULTIPLE] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]) >>
  irule (coprime_by_prime_factor |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rpt strip_tac >>
  `p' divides (p * a + q * b)` by metis_tac[divides_linear, MULT_COMM] >>
  `p' divides (a * b)` by metis_tac[DIVIDES_MULTIPLE, MULT_COMM] >>
  metis_tac[coprime_common_factor, NOT_PRIME_1]
QED

(* Idea: condition for a number to be coprime with prime power. *)

(* Theorem: prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q) *)
(* Proof:
   If part: prime p /\ 0 < n /\ coprime q (p ** n) ==> ~(p divides q)
      By contradiction, suppose p divides q.
      Note p divides (p ** n)  by prime_divides_self_power, 0 < n
      Thus p = 1               by coprime_common_factor
      This contradicts p <> 1  by NOT_PRIME_1
   Only-if part: prime p /\ 0 < n /\ ~(p divides q) ==> coprime q (p ** n)
      Note coprime q p         by prime_not_divides_coprime, GCD_SYM
      Thus coprime q (p ** n)  by coprime_iff_coprime_exp, 0 < n
*)
Theorem coprime_prime_power:
  !p n. prime p /\ 0 < n ==> !q. coprime q (p ** n) <=> ~(p divides q)
Proof
  rw[EQ_IMP_THM] >-
  metis_tac[prime_divides_self_power, coprime_common_factor, NOT_PRIME_1] >>
  metis_tac[prime_not_divides_coprime, coprime_iff_coprime_exp, GCD_SYM]
QED

(* Theorem: prime n ==> !m. 0 < m /\ m < n ==> coprime n m *)
(* Proof:
   By contradiction. Let d = gcd n m, and d <> 1.
   Since prime n, 0 < n       by PRIME_POS
   Thus d divides n, and d m divides    by GCD_IS_GREATEST_COMMON_DIVISOR, n <> 0, m <> 0.
   ==>  d = n                           by prime_def, d <> 1.
   ==>  n divides m                     by d divides m
   ==>  n <= m                          by DIVIDES_LE
   which contradicts m < n.
*)
val prime_coprime_all_lt = store_thm(
  "prime_coprime_all_lt",
  ``!n. prime n ==> !m. 0 < m /\ m < n ==> coprime n m``,
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd n m` >>
  `0 < n` by rw[PRIME_POS] >>
  `n <> 0 /\ m <> 0` by decide_tac >>
  `d divides n /\ d divides m` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d = n` by metis_tac[prime_def] >>
  `n <= m` by rw[DIVIDES_LE] >>
  decide_tac);

(* Theorem: prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j) *)
(* Proof:
   Since m < n, all j < n.
   Hence true by prime_coprime_all_lt
*)
val prime_coprime_all_less = store_thm(
  "prime_coprime_all_less",
  ``!m n. prime n /\ m < n ==> (!j. 0 < j /\ j <= m ==> coprime n j)``,
  rpt strip_tac >>
  `j < n` by decide_tac >>
  rw[prime_coprime_all_lt]);

(* Theorem: prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)) *)
(* Proof:
   If part: prime n ==> 1 < n /\ !j. 0 < j /\ j < n ==> coprime n j
      (1) prime n ==> 1 < n                          by ONE_LT_PRIME
      (2) prime n /\ 0 < j /\ j < n ==> coprime n j  by prime_coprime_all_lt
   Only-if part: !j. 0 < j /\ j < n ==> coprime n j ==> prime n
      By contradiction, assume ~prime n.
      Now, 1 < n /\ ~prime n
      ==> ?p. prime p /\ p < n /\ p divides n   by PRIME_FACTOR_PROPER
      and prime p ==> 0 < p and 1 < p           by PRIME_POS, ONE_LT_PRIME
      Hence ~coprime p n                        by coprime_not_divides, 1 < p
      But 0 < p < n ==> coprime n p             by given implication
      This is a contradiction                   by coprime_sym
*)
val prime_iff_coprime_all_lt = store_thm(
  "prime_iff_coprime_all_lt",
  ``!n. prime n <=> 1 < n /\ (!j. 0 < j /\ j < n ==> coprime n j)``,
  rw[EQ_IMP_THM, ONE_LT_PRIME] >-
  rw[prime_coprime_all_lt] >>
  spose_not_then strip_assume_tac >>
  `?p. prime p /\ p < n /\ p divides n` by rw[PRIME_FACTOR_PROPER] >>
  `0 < p` by rw[PRIME_POS] >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  metis_tac[coprime_not_divides, coprime_sym]);

(* Theorem: prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) *)
(* Proof:
   If part: prime n ==> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))
      Note 1 < n                 by ONE_LT_PRIME
      By contradiction, suppose j divides n.
      Then j = 1 or j = n        by prime_def
      This contradicts 1 < j /\ j < n.
   Only-if part: (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n))) ==> prime n
      This is to show:
      !b. b divides n ==> b = 1 or b = n    by prime_def
      Since 1 < n, so n <> 0     by arithmetic
      Thus b <= n                by DIVIDES_LE
       and b <> 0                by ZERO_DIVIDES
      By contradiction, suppose b <> 1 and b <> n, but b divides n.
      Then 1 < b /\ b < n        by above
      giving ~(b divides n)      by implication
      This contradicts with b divides n.
*)
val prime_iff_no_proper_factor = store_thm(
  "prime_iff_no_proper_factor",
  ``!n. prime n <=> (1 < n /\ (!j. 1 < j /\ j < n ==> ~(j divides n)))``,
  rw_tac std_ss[EQ_IMP_THM] >-
  rw[ONE_LT_PRIME] >-
  metis_tac[prime_def, LESS_NOT_EQ] >>
  rw[prime_def] >>
  `b <= n` by rw[DIVIDES_LE] >>
  `n <> 0` by decide_tac >>
  `b <> 0` by metis_tac[ZERO_DIVIDES] >>
  spose_not_then strip_assume_tac >>
  `1 < b /\ b < n` by decide_tac >>
  metis_tac[]);

(* Theorem: !n. ?p. prime p /\ n < p *)
(* Proof:
   Since ?i. n < PRIMES i   by NEXT_LARGER_PRIME
     and prime (PRIMES i)   by primePRIMES
   Take p = PRIMES i.
*)
val prime_always_bigger = store_thm(
  "prime_always_bigger",
  ``!n. ?p. prime p /\ n < p``,
  metis_tac[NEXT_LARGER_PRIME, primePRIMES]);

(* Theorem: n divides m ==> coprime n (SUC m) *)
(* Proof:
   If n = 0,
     then m = 0      by ZERO_DIVIDES
     gcd 0 (SUC 0)
   = SUC 0           by GCD_0L
   = 1               by ONE
   If n = 1,
      gcd 1 (SUC m) = 1      by GCD_1
   If n <> 0,
     gcd n (SUC m)
   = gcd ((SUC m) MOD n) n   by GCD_EFFICIENTLY
   = gcd 1 n                 by n divides m
   = 1                       by GCD_1
*)
val divides_imp_coprime_with_successor = store_thm(
  "divides_imp_coprime_with_successor",
  ``!m n. n divides m ==> coprime n (SUC m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[GSYM ZERO_DIVIDES] >>
  Cases_on `n = 1` >-
  rw[] >>
  `0 < n /\ 1 < n` by decide_tac >>
  `m MOD n = 0` by rw[GSYM DIVIDES_MOD_0] >>
  `(SUC m) MOD n = (m + 1) MOD n` by rw[ADD1] >>
  `_ = (m MOD n + 1 MOD n) MOD n` by rw[MOD_PLUS] >>
  `_ = (0 + 1) MOD n` by rw[ONE_MOD] >>
  `_ = 1` by rw[ONE_MOD] >>
  metis_tac[GCD_EFFICIENTLY, GCD_1]);

(* Note: counter-example for converse: gcd 3 11 = 1, but ~(3 divides 10). *)

(* Theorem: 0 < m /\ n divides m ==> coprime n (PRE m) *)
(* Proof:
   Since n divides m
     ==> ?q. m = q * n      by divides_def
    Also 0 < m means m <> 0,
     ==> ?k. m = SUC k      by num_CASES
               = k + 1      by ADD1
      so m - k = 1, k = PRE m.
    Let d = gcd n k.
    Then d divides n /\ d divides k     by GCD_IS_GREATEST_COMMON_DIVISOR
     and d divides n ==> d divides m    by DIVIDES_MULTIPLE, m = q * n
      so d divides (m - k)              by DIVIDES_SUB
      or d divides 1                    by m - k = 1
     ==> d = 1                          by DIVIDES_ONE
*)
val divides_imp_coprime_with_predecessor = store_thm(
  "divides_imp_coprime_with_predecessor",
  ``!m n. 0 < m /\ n divides m ==> coprime n (PRE m)``,
  rpt strip_tac >>
  `?q. m = q * n` by rw[GSYM divides_def] >>
  `m <> 0` by decide_tac >>
  `?k. m = k + 1` by metis_tac[num_CASES, ADD1] >>
  `(k = PRE m) /\ (m - k = 1)` by decide_tac >>
  qabbrev_tac `d = gcd n k` >>
  `d divides n /\ d divides k` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d divides m` by rw[DIVIDES_MULTIPLE] >>
  `d divides (m - k)` by rw[DIVIDES_SUB] >>
  metis_tac[DIVIDES_ONE]);

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
   Note coprime p n means coprime n p     by GCD_SYM
     gcd (p * m) n
   = gcd n (p * m)                        by GCD_SYM
   = gcd n p                              by GCD_CANCEL_MULT
*)
val gcd_coprime_cancel = store_thm(
  "gcd_coprime_cancel",
  ``!m n p. coprime p n ==> (gcd (p * m) n = gcd m n)``,
  rw[GCD_CANCEL_MULT, GCD_SYM]);

(* The following is a direct, but tricky, proof of the above result *)

(* Theorem: coprime p n ==> (gcd (p * m) n = gcd m n) *)
(* Proof:
     gcd (p * m) n
   = gcd (p * m) (n * 1)            by MULT_RIGHT_1
   = gcd (p * m) (n * (gcd m 1))    by GCD_1
   = gcd (p * m) (gcd (n * m) n)    by GCD_COMMON_FACTOR
   = gcd (gcd (p * m) (n * m)) n    by GCD_ASSOC
   = gcd (m * (gcd p n)) n          by GCD_COMMON_FACTOR, MULT_COMM
   = gcd (m * 1) n                  by coprime p n
   = gcd m n                        by MULT_RIGHT_1

   Simple proof of GCD_CANCEL_MULT:
   (a*c, b) = (a*c , b*1) = (a * c, b * (c, 1)) = (a * c, b * c, b) = ((a, b) * c, b) = (c, b) since (a,b) = 1.
*)
Theorem gcd_coprime_cancel[allow_rebind]:
  !m n p. coprime p n ==> (gcd (p * m) n = gcd m n)
Proof
  rpt strip_tac >>
  ‘gcd (p * m) n = gcd (p * m) (n * (gcd m 1))’ by rw[GCD_1] >>
  ‘_ = gcd (p * m) (gcd (n * m) n)’ by rw[GSYM GCD_COMMON_FACTOR] >>
  ‘_ = gcd (gcd (p * m) (n * m)) n’ by rw[GCD_ASSOC] >>
  ‘_ = gcd m n’ by rw[GCD_COMMON_FACTOR, MULT_COMM] >>
  rw[]
QED

(* Theorem: prime p /\ prime q /\ p <> q ==> coprime p q *)
(* Proof:
   Let d = gcd p q.
   By contradiction, suppose d <> 1.
   Then d divides p /\ d divides q   by GCD_PROPERTY
     so d = 1 or d = p               by prime_def
    and d = 1 or d = q               by prime_def
    But p <> q                       by given
     so d = 1, contradicts d <> 1.
*)
val primes_coprime = store_thm(
  "primes_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> coprime p q``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd p q` >>
  `d divides p /\ d divides q` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_def]);

(* Theorem: FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) *)
(* Proof:
   By finite induction on s.
   Base: coprime x (PROD_SET {})
      Note PROD_SET {} = 1         by PROD_SET_EMPTY
       and coprime x 1 = T         by GCD_1
   Step: !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s) ==>
        e NOTIN s /\ x NOTIN e INSERT s /\ !z. z IN e INSERT s ==> coprime x z ==>
        coprime x (PROD_SET (e INSERT s))
      Note coprime x e                               by IN_INSERT
       and coprime x (PROD_SET s)                    by induction hypothesis
      Thus coprime x (e * PROD_SET s)                by coprime_product_coprime_sym
        or coprime x PROD_SET (e INSERT s)           by PROD_SET_INSERT
*)
val every_coprime_prod_set_coprime = store_thm(
  "every_coprime_prod_set_coprime",
  ``!s. FINITE s ==> !x. x NOTIN s /\ (!z. z IN s ==> coprime x z) ==> coprime x (PROD_SET s)``,
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  rw[PROD_SET_INSERT, coprime_product_coprime_sym]);

(* ------------------------------------------------------------------------- *)
(* Pairwise Coprime Property                                                 *)
(* ------------------------------------------------------------------------- *)

(* Overload pairwise coprime set *)
val _ = overload_on("PAIRWISE_COPRIME", ``\s. !x y. x IN s /\ y IN s /\ x <> y ==> coprime x y``);

(* Theorem: e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
            (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s *)
(* Proof: by IN_INSERT *)
val pairwise_coprime_insert = store_thm(
  "pairwise_coprime_insert",
  ``!s e. e NOTIN s /\ PAIRWISE_COPRIME (e INSERT s) ==>
        (!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s``,
  metis_tac[IN_INSERT]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s) *)
(* Proof:
   Note FINITE t    by SUBSET_FINITE
   By finite induction on t.
   Base case: PROD_SET {} divides PROD_SET s
      Note PROD_SET {} = 1           by PROD_SET_EMPTY
       and 1 divides (PROD_SET s)    by ONE_DIVIDES_ALL
   Step case: t SUBSET s ==> PROD_SET t divides PROD_SET s ==>
              e NOTIN t /\ e INSERT t SUBSET s ==> PROD_SET (e INSERT t) divides PROD_SET s
      Let m = PROD_SET s.
      Note e IN s /\ t SUBSET s                      by INSERT_SUBSET
      Thus e divides m                               by PROD_SET_ELEMENT_DIVIDES
       and (PROD_SET t) divides m                    by induction hypothesis
      Also coprime e (PROD_SET t)                    by every_coprime_prod_set_coprime, SUBSET_DEF
      Note PROD_SET (e INSERT t) = e * PROD_SET t    by PROD_SET_INSERT
       ==> e * PROD_SET t divides m                  by coprime_product_divides
*)
val pairwise_coprime_prod_set_subset_divides = store_thm(
  "pairwise_coprime_prod_set_subset_divides",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !t. t SUBSET s ==> (PROD_SET t) divides (PROD_SET s)``,
  rpt strip_tac >>
  `FINITE t` by metis_tac[SUBSET_FINITE] >>
  qpat_x_assum `t SUBSET s` mp_tac >>
  qpat_x_assum `FINITE t` mp_tac >>
  qid_spec_tac `t` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  rw[PROD_SET_EMPTY] >>
  fs[] >>
  `e divides PROD_SET s` by rw[PROD_SET_ELEMENT_DIVIDES] >>
  `coprime e (PROD_SET t)` by prove_tac[every_coprime_prod_set_coprime, SUBSET_DEF] >>
  rw[PROD_SET_INSERT, coprime_product_divides]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==>
            !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) *)
(* Proof:
   By finite induction on s.
   Base: {} = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note u = {} and v = {}       by EMPTY_UNION
       and PROD_SET {} = 1         by PROD_SET_EMPTY
      Hence true                   by GCD_1
   Step: PAIRWISE_COPRIME s ==>
         !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v) ==>
         e NOTIN s /\ e INSERT s = u UNION v ==> coprime (PROD_SET u) (PROD_SET v)
      Note (!x. x IN s ==> coprime e x) /\
           PAIRWISE_COPRIME s      by IN_INSERT
      Note e IN u \/ e IN v        by IN_INSERT, IN_UNION
      If e IN u,
         Then e NOTIN v            by IN_DISJOINT
         Let w = u DELETE e.
         Then e NOTIN w            by IN_DELETE
          and u = e INSERT w       by INSERT_DELETE
         Note s = w UNION v        by EXTENSION, IN_INSERT, IN_UNION
          ==> FINITE w             by FINITE_UNION
          and DISJOINT w v         by DISJOINT_INSERT

         Note coprime (PROD_SET w) (PROD_SET v)   by induction hypothesis
          and !x. x IN v ==> coprime e x          by v SUBSET s
         Also FINITE v                            by FINITE_UNION
           so coprime e (PROD_SET v)              by every_coprime_prod_set_coprime, FINITE v
          ==> coprime (e * PROD_SET w) PROD_SET v         by coprime_product_coprime
           or coprime PROD_SET (e INSERT w) PROD_SET v    by PROD_SET_INSERT
            = coprime PROD_SET u PROD_SET v               by above

      Similarly for e IN v.
*)
val pairwise_coprime_partition_coprime = store_thm(
  "pairwise_coprime_partition_coprime",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==>
   !u v. (s = u UNION v) /\ DISJOINT u v ==> coprime (PROD_SET u) (PROD_SET v)``,
  ntac 2 strip_tac >>
  qpat_x_assum `PAIRWISE_COPRIME s` mp_tac >>
  qpat_x_assum `FINITE s` mp_tac >>
  qid_spec_tac `s` >>
  Induct_on `FINITE` >>
  rpt strip_tac >-
  fs[PROD_SET_EMPTY] >>
  `(!x. x IN s ==> coprime e x) /\ PAIRWISE_COPRIME s` by metis_tac[IN_INSERT] >>
  `e IN u \/ e IN v` by metis_tac[IN_INSERT, IN_UNION] >| [
    qabbrev_tac `w = u DELETE e` >>
    `u = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN v` by metis_tac[IN_DISJOINT] >>
    `s = w UNION v` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT w v` by metis_tac[DISJOINT_INSERT] >>
    `coprime (PROD_SET w) (PROD_SET v)` by rw[] >>
    `(!x. x IN v ==> coprime e x)` by rw[] >>
    `FINITE v` by metis_tac[FINITE_UNION] >>
    `coprime e (PROD_SET v)` by rw[every_coprime_prod_set_coprime] >>
    metis_tac[coprime_product_coprime, PROD_SET_INSERT],
    qabbrev_tac `w = v DELETE e` >>
    `v = e INSERT w` by rw[Abbr`w`] >>
    `e NOTIN w` by rw[Abbr`w`] >>
    `e NOTIN u` by metis_tac[IN_DISJOINT] >>
    `s = u UNION w` by
  (rw[EXTENSION] >>
    metis_tac[IN_INSERT, IN_UNION]) >>
    `FINITE w` by metis_tac[FINITE_UNION] >>
    `DISJOINT u w` by metis_tac[DISJOINT_INSERT, DISJOINT_SYM] >>
    `coprime (PROD_SET u) (PROD_SET w)` by rw[] >>
    `(!x. x IN u ==> coprime e x)` by rw[] >>
    `FINITE u` by metis_tac[FINITE_UNION] >>
    `coprime (PROD_SET u) e` by rw[every_coprime_prod_set_coprime, coprime_sym] >>
    metis_tac[coprime_product_coprime_sym, PROD_SET_INSERT]
  ]);

(* Theorem: FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
            (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v)) *)
(* Proof: by PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime *)
val pairwise_coprime_prod_set_partition = store_thm(
  "pairwise_coprime_prod_set_partition",
  ``!s. FINITE s /\ PAIRWISE_COPRIME s ==> !u v. (s = u UNION v) /\ DISJOINT u v ==>
       (PROD_SET s = PROD_SET u * PROD_SET v) /\ (coprime (PROD_SET u) (PROD_SET v))``,
  metis_tac[PROD_SET_PRODUCT_BY_PARTITION, pairwise_coprime_partition_coprime]);

(* ------------------------------------------------------------------------- *)
(* GCD divisibility condition of Power Predecessors                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)) *)
(* Proof:
   Note !n. 1 <= t ** n                  by ONE_LE_EXP, 0 < t, [1]

   Claim: t ** (n - m) - 1 <= t ** n - 1, because:
   Proof: Note n - m <= n                always
            so t ** (n - m) <= t ** n    by EXP_BASE_LEQ_MONO_IMP, 0 < t
           Now 1 <= t ** (n - m) and
               1 <= t ** n               by [1]
           Hence t ** (n - m) - 1 <= t ** n - 1.

        t ** (n - m) * (t ** m - 1) + t ** (n - m) - 1
      = (t ** (n - m) * t ** m - t ** (n - m)) + t ** (n - m) - 1   by LEFT_SUB_DISTRIB
      = (t ** (n - m + m) - t ** (n - m)) + t ** (n - m) - 1        by EXP_ADD
      = (t ** n - t ** (n - m)) + t ** (n - m) - 1                  by SUB_ADD, m <= n
      = (t ** n - (t ** (n - m) - 1 + 1)) + t ** (n - m) - 1        by SUB_ADD, 1 <= t ** (n - m)
      = (t ** n - (1 + (t ** (n - m) - 1))) + t ** (n - m) - 1      by ADD_COMM
      = (t ** n - 1 - (t ** (n - m) - 1)) + t ** (n - m) - 1        by SUB_PLUS, no condition
      = t ** n - 1                                 by SUB_ADD, t ** (n - m) - 1 <= t ** n - 1
*)
val power_predecessor_division_eqn = store_thm(
  "power_predecessor_division_eqn",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1))``,
  rpt strip_tac >>
  `1 <= t ** n /\ 1 <= t ** (n - m)` by rw[ONE_LE_EXP] >>
  `n - m <= n` by decide_tac >>
  `t ** (n - m) <= t ** n` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `t ** (n - m) - 1 <= t ** n - 1` by decide_tac >>
  qabbrev_tac `z = t ** (n - m) - 1` >>
  `t ** (n - m) * (t ** m - 1) + z =
    t ** (n - m) * t ** m - t ** (n - m) + z` by decide_tac >>
  `_ = t ** (n - m + m) - t ** (n - m) + z` by rw_tac std_ss[EXP_ADD] >>
  `_ = t ** n - t ** (n - m) + z` by rw_tac std_ss[SUB_ADD] >>
  `_ = t ** n - (z + 1) + z` by rw_tac std_ss[SUB_ADD, Abbr`z`] >>
  `_ = t ** n + z - (z + 1)` by decide_tac >>
  `_ = t ** n - 1` by decide_tac >>
  decide_tac);

(* This shows the pattern:
                    1000000    so 9999999999 = 1000000 * 9999 + 999999
               ------------    or (b ** 10 - 1) = b ** 6 * (b ** 4 - 1) + (b ** 6 - 1)
          9999 | 9999999999    where b = 10.
                 9999
                 ----------
                     999999
*)

(* Theorem: 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1) *)
(* Proof: by power_predecessor_division_eqn *)
val power_predecessor_division_alt = store_thm(
  "power_predecessor_division_alt",
  ``!t m n. 0 < t /\ m <= n ==>
           (t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1)``,
  rpt strip_tac >>
  imp_res_tac power_predecessor_division_eqn >>
  fs[]);

(* Theorem: m < n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)) *)
(* Proof:
   Case t = 0,
      If n = 0, t ** 0 = 1             by ZERO_EXP
      LHS = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
      If n <> 0, 0 ** n = 0            by ZERO_EXP
      LHS = gcd (0 - 1) x
          = gcd 0 x = 0                by GCD_0L
          = gcd 0 y = RHS              by ZERO_EXP
   Case t <> 0,
      Note t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)
                                       by power_predecessor_division_eqn
        so t ** (n - m) * (t ** m - 1) <= t ** n - 1    by above, [1]
       and t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1, [2]
        gcd (t ** n - 1) (t ** m - 1)
      = gcd (t ** m - 1) (t ** n - 1)                by GCD_SYM
      = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))
                                                     by GCD_SUB_MULTIPLE, [1]
      = gcd (t ** m - 1)) (t ** (n - m) - 1)         by [2]
*)
val power_predecessor_gcd_reduction = store_thm(
  "power_predecessor_gcd_reduction",
  ``!t n m. m <= n ==> (gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1))``,
  rpt strip_tac >>
  Cases_on `t = 0` >-
  rw[ZERO_EXP] >>
  `t ** n - 1 = t ** (n - m) * (t ** m - 1) + (t ** (n - m) - 1)` by rw[power_predecessor_division_eqn] >>
  `t ** n - 1 - t ** (n - m) * (t ** m - 1) = t ** (n - m) - 1` by fs[] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd (t ** m - 1) (t ** n - 1)` by rw_tac std_ss[GCD_SYM] >>
  `_ = gcd (t ** m - 1) ((t ** n - 1) - t ** (n - m) * (t ** m - 1))` by rw_tac std_ss[GCD_SUB_MULTIPLE] >>
  rw_tac std_ss[]);

(* Theorem: gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1 *)
(* Proof:
   By complete induction on (n + m):
   Induction hypothesis: !m'. m' < n + m ==>
                         !n m. (m' = n + m) ==> (gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1)
   Idea: if 0 < m, n < n + m. Put last n = m, m = n - m. That is m' = m + (n - m) = n.
   Also  if 0 < n, m < n + m. Put last n = n, m = m - n. That is m' = n + (m - n) = m.

   Thus to apply induction hypothesis, need 0 < n or 0 < m.
   So take care of these special cases first.

   Case: n = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** 0 - 1) (t ** m - 1)
             = gcd 0 (t ** m - 1)                 by EXP
             = t ** m - 1                         by GCD_0L
             = t ** (gcd 0 m) - 1 = RHS           by GCD_0L
   Case: m = 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** n - 1) (t ** 0 - 1)
             = gcd (t ** n - 1) 0                 by EXP
             = t ** n - 1                         by GCD_0R
             = t ** (gcd n 0) - 1 = RHS           by GCD_0R

   Case: m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
      That is, 0 < n, and 0 < m
          also n < n + m, and m < n + m           by arithmetic

      Use trichotomy of numbers:                  by LESS_LESS_CASES
      Case: n = m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         LHS = gcd (t ** m - 1) (t ** m - 1)
             = t ** m - 1                         by GCD_REF
             = t ** (gcd m m) - 1 = RHS           by GCD_REF

      Case: m < n /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since n < n + m                          by 0 < m
           and m + (n - m) = (n - m) + m          by ADD_COMM
                           = n                    by SUB_ADD, m <= n
           gcd (t ** n - 1) (t ** m - 1)
         = gcd ((t ** m - 1)) (t ** (n - m) - 1)  by power_predecessor_gcd_reduction
         = t ** gcd m (n - m) - 1                 by induction hypothesis, m + (n - m) = n
         = t ** gcd m n - 1                       by GCD_SUB_R, m <= n
         = t ** gcd n m - 1                       by GCD_SYM

      Case: n < m /\ m <> 0 /\ n <> 0 ==> gcd (t ** n - 1) (t ** m - 1) = t ** gcd n m - 1
         Since m < n + m                          by 0 < n
           and n + (m - n) = (m - n) + n          by ADD_COMM
                           = m                    by SUB_ADD, n <= m
          gcd (t ** n - 1) (t ** m - 1)
        = gcd (t ** m - 1) (t ** n - 1)           by GCD_SYM
        = gcd ((t ** n - 1)) (t ** (m - n) - 1)   by power_predecessor_gcd_reduction
        = t ** gcd n (m - n) - 1                  by induction hypothesis, n + (m - n) = m
        = t ** gcd n m                            by GCD_SUB_R, n <= m
*)
val power_predecessor_gcd_identity = store_thm(
  "power_predecessor_gcd_identity",
  ``!t n m. gcd (t ** n - 1) (t ** m - 1) = t ** (gcd n m) - 1``,
  rpt strip_tac >>
  completeInduct_on `n + m` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[EXP] >>
  Cases_on `m = 0` >-
  rw[EXP] >>
  `(n = m) \/ (m < n) \/ (n < m)` by metis_tac[LESS_LESS_CASES] >-
  rw[GCD_REF] >-
 (`0 < m /\ n < n + m` by decide_tac >>
  `m <= n` by decide_tac >>
  `m + (n - m) = n` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** m - 1)) (t ** (n - m) - 1)` by rw[power_predecessor_gcd_reduction] >>
  `_ = t ** gcd m (n - m) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R, GCD_SYM]) >>
  `0 < n /\ m < n + m` by decide_tac >>
  `n <= m` by decide_tac >>
  `n + (m - n) = m` by metis_tac[SUB_ADD, ADD_COMM] >>
  `gcd (t ** n - 1) (t ** m - 1) = gcd ((t ** n - 1)) (t ** (m - n) - 1)` by rw[power_predecessor_gcd_reduction, GCD_SYM] >>
  `_ = t ** gcd n (m - n) - 1` by metis_tac[] >>
  metis_tac[GCD_SUB_R]);

(* Above is the formal proof of the following pattern:
   For any base
         gcd(999999,9999) = gcd(6 9s, 4 9s) = gcd(6,4) 9s = 2 9s = 99
   or        999999 MOD 9999 = (6 9s) MOD (4 9s) = 2 9s = 99
   Thus in general,
             (m 9s) MOD (n 9s) = (m MOD n) 9s
   Repeating the use of Euclidean algorithm then gives:
             gcd (m 9s, n 9s) = (gcd m n) 9s

Reference: A Mathematical Tapestry (by Jean Pedersen and Peter Hilton)
Chapter 4: A number-theory thread -- Folding numbers, a number trick, and some tidbits.
*)

(* Theorem: 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m) *)
(* Proof:
       (t ** n - 1) divides (t ** m - 1)
   <=> gcd (t ** n - 1) (t ** m - 1) = t ** n - 1   by divides_iff_gcd_fix
   <=> t ** (gcd n m) - 1 = t ** n - 1              by power_predecessor_gcd_identity
   <=> t ** (gcd n m) = t ** n                      by PRE_SUB1, INV_PRE_EQ, EXP_POS, 0 < t
   <=>       gcd n m = n                            by EXP_BASE_INJECTIVE, 1 < t
   <=>       n divides m                            by divides_iff_gcd_fix
*)
val power_predecessor_divisibility = store_thm(
  "power_predecessor_divisibility",
  ``!t n m. 1 < t ==> ((t ** n - 1) divides (t ** m - 1) <=> n divides m)``,
  rpt strip_tac >>
  `0 < t` by decide_tac >>
  `!n. 0 < t ** n` by rw[EXP_POS] >>
  `!x y. 0 < x /\ 0 < y ==> ((x - 1 = y - 1) <=> (x = y))` by decide_tac >>
  `(t ** n - 1) divides (t ** m - 1) <=> ((gcd (t ** n - 1) (t ** m - 1) = t ** n - 1))` by rw[divides_iff_gcd_fix] >>
  `_ = (t ** (gcd n m) - 1 = t ** n - 1)` by rw[power_predecessor_gcd_identity] >>
  `_ = (t ** (gcd n m) = t ** n)` by rw[] >>
  `_ = (gcd n m = n)` by rw[EXP_BASE_INJECTIVE] >>
  rw[divides_iff_gcd_fix]);

(* Theorem: t - 1 divides t ** n - 1 *)
(* Proof:
   If t = 0,
      Then t - 1 = 0        by integer subtraction
       and t ** n - 1 = 0   by ZERO_EXP, either case of n.
      Thus 0 divides 0      by ZERO_DIVIDES
   If t = 1,
      Then t - 1 = 0        by arithmetic
       and t ** n - 1 = 0   by EXP_1
      Thus 0 divides 0      by ZERO_DIVIDES
   Otherwise, 1 < t
       and 1 divides n      by ONE_DIVIDES_ALL
       ==> t ** 1 - 1 divides t ** n - 1   by power_predecessor_divisibility
        or      t - 1 divides t ** n - 1   by EXP_1
*)
Theorem power_predecessor_divisor:
  !t n. t - 1 divides t ** n - 1
Proof
  rpt strip_tac >>
  Cases_on `t = 0` >-
  simp[ZERO_EXP] >>
  Cases_on `t = 1` >-
  simp[] >>
  `1 < t` by decide_tac >>
  metis_tac[power_predecessor_divisibility, EXP_1, ONE_DIVIDES_ALL]
QED

(* Overload power predecessor *)
Overload tops = “\b:num n. b ** n - 1”

(*
   power_predecessor_division_eqn
     |- !t m n. 0 < t /\ m <= n ==> tops t n = t ** (n - m) * tops t m + tops t (n - m)
   power_predecessor_division_alt
     |- !t m n. 0 < t /\ m <= n ==> tops t n - t ** (n - m) * tops t m = tops t (n - m)
   power_predecessor_gcd_reduction
     |- !t n m. m <= n ==> (gcd (tops t n) (tops t m) = gcd (tops t m) (tops t (n - m)))
   power_predecessor_gcd_identity
     |- !t n m. gcd (tops t n) (tops t m) = tops t (gcd n m)
   power_predecessor_divisibility
     |- !t n m. 1 < t ==> (tops t n divides tops t m <=> n divides m)
   power_predecessor_divisor
     |- !t n. t - 1 divides tops t n
*)

(* Overload power predecessor base 10 *)
val _ = overload_on("nines", ``\n. tops 10 n``);

(* Obtain corollaries *)

val nines_division_eqn = save_thm("nines_division_eqn",
    power_predecessor_division_eqn |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_division_alt = save_thm("nines_division_alt",
    power_predecessor_division_alt |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_gcd_reduction = save_thm("nines_gcd_reduction",
    power_predecessor_gcd_reduction |> ISPEC ``10``);
val nines_gcd_identity = save_thm("nines_gcd_identity",
    power_predecessor_gcd_identity |> ISPEC ``10``);
val nines_divisibility = save_thm("nines_divisibility",
    power_predecessor_divisibility |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
val nines_divisor = save_thm("nines_divisor",
    power_predecessor_divisor |> ISPEC ``10`` |> SIMP_RULE (srw_ss()) []);
(*
val nines_division_eqn =
   |- !m n. m <= n ==> nines n = 10 ** (n - m) * nines m + nines (n - m): thm
val nines_division_alt =
   |- !m n. m <= n ==> nines n - 10 ** (n - m) * nines m = nines (n - m): thm
val nines_gcd_reduction =
   |- !n m. m <= n ==> gcd (nines n) (nines m) = gcd (nines m) (nines (n - m)): thm
val nines_gcd_identity = |- !n m. gcd (nines n) (nines m) = nines (gcd n m): thm
val nines_divisibility = |- !n m. nines n divides nines m <=> n divides m: thm
val nines_divisor = |- !n. 9 divides nines n: thm
*)

(* ------------------------------------------------------------------------- *)
(* GCD involving Powers                                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime m /\ prime n /\ m divides (n ** k) ==> (m = n) *)
(* Proof:
   By induction on k.
   Base: m divides n ** 0 ==> (m = n)
      Since n ** 0 = 1              by EXP
        and m divides 1 ==> m = 1   by DIVIDES_ONE
       This contradicts 1 < m       by ONE_LT_PRIME
   Step: m divides n ** k ==> (m = n) ==> m divides n ** SUC k ==> (m = n)
      Since n ** SUC k = n * n ** k           by EXP
       Also m divides n \/ m divides n ** k   by P_EUCLIDES
         If m divides n, then m = n           by prime_divides_only_self
         If m divides n ** k, then m = n      by induction hypothesis
*)
val prime_divides_prime_power = store_thm(
  "prime_divides_prime_power",
  ``!m n k. prime m /\ prime n /\ m divides (n ** k) ==> (m = n)``,
  rpt strip_tac >>
  Induct_on `k` >| [
    rpt strip_tac >>
    `1 < m` by rw[ONE_LT_PRIME] >>
    `m = 1` by metis_tac[EXP, DIVIDES_ONE] >>
    decide_tac,
    metis_tac[EXP, P_EUCLIDES, prime_divides_only_self]
  ]);

(* This is better than FACTOR_OUT_PRIME *)

(* Theorem: 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q *)
(* Proof:
   If p divides n,
      Then ?m. 0 < m /\ p ** m divides n /\
           !k. coprime (p ** k) (n DIV p ** m)   by FACTOR_OUT_PRIME
      Let q = n DIV (p ** m).
      Note 0 < p                                 by PRIME_POS
        so 0 < p ** m                            by EXP_POS, 0 < p
      Take this q and m,
      Then n = (p ** m) * q                      by DIVIDES_EQN_COMM
       and coprime p q                           by taking k = 1, EXP_1

   If ~(p divides n),
      Then coprime p n                           by prime_not_divides_coprime
      Let q = n, m = 0.
      Then n = 1 * q                             by EXP, MULT_LEFT_1
       and coprime p q.
*)
val prime_power_factor = store_thm(
  "prime_power_factor",
  ``!n p. 0 < n /\ prime p ==> ?q m. (n = (p ** m) * q) /\ coprime p q``,
  rpt strip_tac >>
  Cases_on `p divides n` >| [
    `?m. 0 < m /\ p ** m divides n /\ !k. coprime (p ** k) (n DIV p ** m)` by rw[FACTOR_OUT_PRIME] >>
    qabbrev_tac `q = n DIV (p ** m)` >>
    `0 < p` by rw[PRIME_POS] >>
    `0 < p ** m` by rw[EXP_POS] >>
    metis_tac[DIVIDES_EQN_COMM, EXP_1],
    `coprime p n` by rw[prime_not_divides_coprime] >>
    metis_tac[EXP, MULT_LEFT_1]
  ]);

(* Even this simple theorem is quite difficult to prove, why? *)
(* Because this needs a typical detective-style proof! *)

(* Theorem: prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j) *)
(* Proof:
   Note 0 < p                by PRIME_POS
     so 0 < p ** n           by EXP_POS
   Thus 0 < a                by ZERO_DIVIDES
    ==> ?q m. (a = (p ** m) * q) /\ coprime p q    by prime_power_factor

   Claim: q = 1
   Proof: By contradiction, suppose q <> 1.
          Then ?t. prime t /\ t divides q          by PRIME_FACTOR, q <> 1
           Now q divides a           by divides_def
            so t divides (p ** n)    by DIVIDES_TRANS
           ==> t = p                 by prime_divides_prime_power
           But gcd t q = t           by divides_iff_gcd_fix
            or gcd p q = p           by t = p
           Yet p <> 1                by NOT_PRIME_1
            so this contradicts coprime p q.

   Thus a = p ** m                   by q = 1, Claim.
   Note p ** m <= p ** n             by DIVIDES_LE, 0 < p
    and 1 < p                        by ONE_LT_PRIME
    ==>      m <= n                  by EXP_BASE_LE_MONO, 1 < p
   Take j = m, and the result follows.
*)
val prime_power_divisor = store_thm(
  "prime_power_divisor",
  ``!p n a. prime p /\ a divides (p ** n) ==> ?j. j <= n /\ (a = p ** j)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  `0 < p ** n` by rw[EXP_POS] >>
  `0 < a` by metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO] >>
  `?q m. (a = (p ** m) * q) /\ coprime p q` by rw[prime_power_factor] >>
  `q = 1` by
  (spose_not_then strip_assume_tac >>
  `?t. prime t /\ t divides q` by rw[PRIME_FACTOR] >>
  `q divides a` by metis_tac[divides_def] >>
  `t divides (p ** n)` by metis_tac[DIVIDES_TRANS] >>
  `t = p` by metis_tac[prime_divides_prime_power] >>
  `gcd t q = t` by rw[GSYM divides_iff_gcd_fix] >>
  metis_tac[NOT_PRIME_1]) >>
  `a = p ** m` by rw[] >>
  metis_tac[DIVIDES_LE, EXP_BASE_LE_MONO, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q ==>
            !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n) *)
(* Proof:
   First goal: p = q.
      Since p divides p        by DIVIDES_REFL
        ==> p divides p ** m   by divides_exp, 0 < m.
         so p divides q ** n   by given, p ** m = q ** n
      Hence p = q              by prime_divides_prime_power
   Second goal: m = n.
      Note p = q               by first goal.
      Since 1 < p              by ONE_LT_PRIME
      Hence m = n              by EXP_BASE_INJECTIVE, 1 < p
*)
val prime_powers_eq = store_thm(
  "prime_powers_eq",
  ``!p q. prime p /\ prime q ==>
   !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n)``,
  ntac 6 strip_tac >>
  conj_asm1_tac >-
  metis_tac[divides_exp, prime_divides_prime_power, DIVIDES_REFL] >>
  metis_tac[EXP_BASE_INJECTIVE, ONE_LT_PRIME]);

(* Theorem: prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n) *)
(* Proof:
   Let d = gcd (p ** m) (q ** n).
   By contradiction, d <> 1.
   Then d divides (p ** m) /\ d divides (q ** n)   by GCD_PROPERTY
    ==> ?j. j <= m /\ (d = p ** j)                 by prime_power_divisor, prime p
    and ?k. k <= n /\ (d = q ** k)                 by prime_power_divisor, prime q
   Note j <> 0 /\ k <> 0                           by EXP_0
     or 0 < j /\ 0 < k                             by arithmetic
    ==> p = q, which contradicts p <> q            by prime_powers_eq
*)
val prime_powers_coprime = store_thm(
  "prime_powers_coprime",
  ``!p q. prime p /\ prime q /\ p <> q ==> !m n. coprime (p ** m) (q ** n)``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `d = gcd (p ** m) (q ** n)` >>
  `d divides (p ** m) /\ d divides (q ** n)` by metis_tac[GCD_PROPERTY] >>
  metis_tac[prime_power_divisor, prime_powers_eq, EXP_0, NOT_ZERO_LT_ZERO]);

(*
val prime_powers_eq = |- !p q. prime p /\ prime q ==> !m n. 0 < m /\ (p ** m = q ** n) ==> (p = q) /\ (m = n): thm
*)

(* Theorem: prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n)) *)
(* Proof:
   If part: p ** m divides q ** n ==> (p = q) /\ m <= n
      Note p divides (p ** m)         by prime_divides_self_power, 0 < m
        so p divides (q ** n)         by DIVIDES_TRANS
      Thus p = q                      by prime_divides_prime_power
      Note 1 < p                      by ONE_LT_PRIME
      Thus m <= n                     by power_divides_iff
   Only-if part: (p = q) /\ m <= n ==> p ** m divides q ** n
      Note 1 < p                      by ONE_LT_PRIME
      Thus p ** m divides q ** n      by power_divides_iff
*)
val prime_powers_divide = store_thm(
  "prime_powers_divide",
  ``!p q. prime p /\ prime q ==> !m n. 0 < m ==> ((p ** m divides q ** n) <=> (p = q) /\ (m <= n))``,
  metis_tac[ONE_LT_PRIME, divides_self_power, prime_divides_prime_power, power_divides_iff, DIVIDES_TRANS]);

(* Theorem: gcd (b ** m) (b ** n) = b ** (MIN m n) *)
(* Proof:
   If m = n,
      LHS = gcd (b ** n) (b ** n)
          = b ** n                     by GCD_REF
      RHS = b ** (MIN n n)
          = b ** n                     by MIN_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or gcd (b ** m) (b ** n)
       = b ** m                        by divides_iff_gcd_fix
       = b ** (MIN m n)                by MIN_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use GCD_SYM.
*)
val gcd_powers = store_thm(
  "gcd_powers",
  ``!b m n. gcd (b ** m) (b ** n) = b ** (MIN m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, MIN_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_gcd_fix, GCD_SYM, MIN_DEF]
  ]);

(* Theorem: lcm (b ** m) (b ** n) = b ** (MAX m n) *)
(* Proof:
   If m = n,
      LHS = lcm (b ** n) (b ** n)
          = b ** n                     by LCM_REF
      RHS = b ** (MAX n n)
          = b ** n                     by MAX_IDEM
   If m < n,
      b ** n = b ** (n - m + m)        by arithmetic
             = b ** (n - m) * b ** m   by EXP_ADD
      so (b ** m) divides (b ** n)     by divides_def
      or lcm (b ** m) (b ** n)
       = b ** n                        by divides_iff_lcm_fix
       = b ** (MAX m n)                by MAX_DEF
   If ~(m < n), n < m.
      Similar argument as m < n, with m n exchanged, use LCM_COMM.
*)
val lcm_powers = store_thm(
  "lcm_powers",
  ``!b m n. lcm (b ** m) (b ** n) = b ** (MAX m n)``,
  rpt strip_tac >>
  Cases_on `m = n` >-
  rw[LCM_REF] >>
  Cases_on `m < n` >| [
    `b ** n = b ** (n - m + m)` by rw[] >>
    `_ = b ** (n - m) * b ** m` by rw[EXP_ADD] >>
    `(b ** m) divides (b ** n)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, MAX_DEF],
    `n < m` by decide_tac >>
    `b ** m = b ** (m - n + n)` by rw[] >>
    `_ = b ** (m - n) * b ** n` by rw[EXP_ADD] >>
    `(b ** n) divides (b ** m)` by metis_tac[divides_def] >>
    metis_tac[divides_iff_lcm_fix, LCM_COMM, MAX_DEF]
  ]);

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n - 1)
      <=> T                                by coprime_PRE

   Claim: !j. j < m ==> coprime (b ** j) (b ** m - 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (PRE (b ** m))  by divides_imp_coprime_with_predecessor
       or coprime (b ** j) (b ** m - 1)    by PRE_SUB1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z - 1)                        by coprime_PRE
     ==> coprime (z ** (n DIV m)) (z - 1)         by coprime_exp
          gcd (b ** n) (b ** m - 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z - 1)
        = gcd (b ** (n MOD m)) (z - 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_predecessor = store_thm(
  "coprime_power_and_power_predecessor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m - 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_PRE] >>
  `!j. j < m ==> coprime (b ** j) (b ** m - 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_predecessor, PRE_SUB1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z - 1)` by rw[coprime_PRE] >>
  `coprime (z ** (n DIV m)) (z - 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* Any counter-example? Theorem proved, no counter-example! *)
(* This is a most unexpected theorem.
   At first I thought it only holds for prime base b,
   but in HOL4 using the EVAL function shows it seems to hold for any base b.
   As for the proof, I don't have a clue initially.
   I try this idea:
   For a prime base b, most likely ODD b, then ODD (b ** n) and ODD (b ** m).
   But then EVEN (b ** m - 1), maybe ODD and EVEN will give coprime.
   If base b is EVEN, then EVEN (b ** n) but ODD (b ** m - 1), so this can work.
   However, in general ODD and EVEN do not give coprime:  gcd 6 9 = 3.
   Of course, if ODD and EVEN arise from powers of same base, like this theorem, then true!
   Actually this follows from divides_imp_coprime_with_predecessor, sort of.
   This success inspires the following theorem.
*)

(* Theorem: 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1) *)
(* Proof:
   If m = n,
          coprime (b ** n) (b ** n + 1)
      <=> T                                by coprime_SUC

   Claim: !j. j < m ==> coprime (b ** j) (b ** m + 1)
   Proof: b ** m
        = b ** (m - j + j)                 by SUB_ADD
        = b ** (m - j) * b ** j            by EXP_ADD
     Thus (b ** j) divides (b ** m)        by divides_def
      Now 0 < b ** m                       by EXP_POS
       so coprime (b ** j) (SUC (b ** m))  by divides_imp_coprime_with_successor
       or coprime (b ** j) (b ** m + 1)    by ADD1

   Given 0 < m,
          b ** n
        = b ** ((n DIV m) * m + n MOD m)          by DIVISION
        = b ** (m * (n DIV m) + n MOD m)          by MULT_COMM
        = b ** (m * (n DIV m)) * b ** (n MOD m)   by EXP_ADD
        = (b ** m) ** (n DIV m) * b ** (n MOD m)  by EXP_EXP_MULT
   Let z = b ** m,
   Then b ** n = z ** (n DIV m) * b ** (n MOD m)
    and 0 < z                                     by EXP_POS
   Since coprime z (z + 1)                        by coprime_SUC
     ==> coprime (z ** (n DIV m)) (z + 1)         by coprime_exp
          gcd (b ** n) (b ** m + 1)
        = gcd (z ** (n DIV m) * b ** (n MOD m)) (z + 1)
        = gcd (b ** (n MOD m)) (z + 1)            by GCD_SYM, GCD_CANCEL_MULT
    Now (n MOD m) < m                             by MOD_LESS
    so apply the claim to deduce the result.
*)
val coprime_power_and_power_successor = store_thm(
  "coprime_power_and_power_successor",
  ``!b m n. 0 < b /\ 0 < m ==> coprime (b ** n) (b ** m + 1)``,
  rpt strip_tac >>
  `0 < b ** n /\ 0 < b ** m` by rw[EXP_POS] >>
  Cases_on `m = n` >-
  rw[coprime_SUC] >>
  `!j. j < m ==> coprime (b ** j) (b ** m + 1)` by
  (rpt strip_tac >>
  `b ** m = b ** (m - j + j)` by rw[] >>
  `_ = b ** (m - j) * b ** j` by rw[EXP_ADD] >>
  `(b ** j) divides (b ** m)` by metis_tac[divides_def] >>
  metis_tac[divides_imp_coprime_with_successor, ADD1]) >>
  `b ** n = b ** ((n DIV m) * m + n MOD m)` by rw[GSYM DIVISION] >>
  `_ = b ** (m * (n DIV m) + n MOD m)` by rw[MULT_COMM] >>
  `_ = b ** (m * (n DIV m)) * b ** (n MOD m)` by rw[EXP_ADD] >>
  `_ = (b ** m) ** (n DIV m) * b ** (n MOD m)` by rw[EXP_EXP_MULT] >>
  qabbrev_tac `z = b ** m` >>
  `coprime z (z + 1)` by rw[coprime_SUC] >>
  `coprime (z ** (n DIV m)) (z + 1)` by rw[coprime_exp] >>
  metis_tac[GCD_SYM, GCD_CANCEL_MULT, MOD_LESS]);

(* ------------------------------------------------------------------------- *)
(* Useful Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q) *)
(* Proof:
   By contradiction, suppose q <> 1 /\ ~(p divides q).
   Note ?j. j <= n /\ (q = p ** j)   by prime_power_divisor
    and 0 < j                        by EXP_0, q <> 1
   then p divides q                  by prime_divides_self_power, 0 < j
   This contradicts ~(p divides q).
*)
Theorem PRIME_EXP_FACTOR:
  !p q n. prime p /\ q divides (p ** n) ==> (q = 1) \/ (p divides q)
Proof
  spose_not_then strip_assume_tac >>
  `?j. j <= n /\ (q = p ** j)` by rw[prime_power_divisor] >>
  `0 < j` by fs[] >>
  metis_tac[prime_divides_self_power]
QED

(* Idea: For prime p, FACT (p-1) MOD p <> 0 *)

(* Theorem: prime p /\ n < p ==> FACT n MOD p <> 0 *)
(* Proof:
   Note 1 < p                  by ONE_LT_PRIME
   By induction on n.
   Base: 0 < p ==> (FACT 0 MOD p = 0) ==> F
      Note FACT 0 = 1          by FACT_0
       and 1 MOD p = 1         by LESS_MOD, 1 < p
       and 1 = 0 is F.
   Step: n < p ==> (FACT n MOD p = 0) ==> F ==>
         SUC n < p ==> (FACT (SUC n) MOD p = 0) ==> F
      If n = 0, SUC 0 = 1      by ONE
         Note FACT 1 = 1       by FACT_1
          and 1 MOD p = 1      by LESS_MOD, 1 < p
          and 1 = 0 is F.
      If n <> 0, 0 < n.
             (FACT (SUC n)) MOD p = 0
         <=> (SUC n * FACT n) MOD p = 0      by FACT
         Note (SUC n) MOD p <> 0             by MOD_LESS, SUC n < p
          and (FACT n) MOD p <> 0            by induction hypothesis
           so (SUC n * FACT n) MOD p <> 0    by EUCLID_LEMMA
         This is a contradiction.
*)
Theorem FACT_MOD_PRIME:
  !p n. prime p /\ n < p ==> FACT n MOD p <> 0
Proof
  rpt strip_tac >>
  `1 < p` by rw[ONE_LT_PRIME] >>
  Induct_on `n` >-
  simp[FACT_0] >>
  Cases_on `n = 0` >-
  simp[FACT_1] >>
  rw[FACT] >>
  `n < p` by decide_tac >>
  `(SUC n) MOD p <> 0` by fs[] >>
  metis_tac[EUCLID_LEMMA]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
