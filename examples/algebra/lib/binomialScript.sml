(* ------------------------------------------------------------------------- *)
(* Binomial coefficients and expansion.                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "binomial";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "helperFunctionTheory"; *)
(* (* val _ = load "helperNumTheory"; -- in helperFunctionTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in helperFunctionTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* val _ = load "helperListTheory"; *)
open helperListTheory;

(* open dependent theories *)
open pred_setTheory listTheory;
(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open arithmeticTheory dividesTheory gcdTheory;


(* ------------------------------------------------------------------------- *)
(* Binomial scripts in HOL:
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\summationScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\powerScript.sml
C:\jc\www\ml\hol\info\Hol\examples\miller\RSA\binomialScript.sml
*)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Binomial Documentation                                                    *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Binomial Coefficients:
   binomial_def        |- (binomial 0 0 = 1) /\ (!n. binomial (SUC n) 0 = 1) /\
                          (!k. binomial 0 (SUC k) = 0) /\
                          !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_alt        |- !n k. binomial n 0 = 1 /\ binomial 0 (k + 1) = 0 /\
                                binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1)
   binomial_less_0     |- !n k. n < k ==> (binomial n k = 0)
   binomial_n_0        |- !n. binomial n 0 = 1
   binomial_n_n        |- !n. binomial n n = 1
   binomial_0_n        |- !n. binomial 0 n = if n = 0 then 1 else 0
   binomial_recurrence |- !n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)
   binomial_formula    |- !n k. binomial (n + k) k * (FACT n * FACT k) = FACT (n + k)
   binomial_formula2   |- !n k. k <= n ==> (FACT n = binomial n k * (FACT (n - k) * FACT k))
   binomial_formula3   |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_fact       |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k)))
   binomial_n_k        |- !n k. k <= n ==> (binomial n k = FACT n DIV FACT k DIV FACT (n - k)
   binomial_n_1        |- !n. binomial n 1 = n
   binomial_sym        |- !n k. k <= n ==> (binomial n k = binomial n (n - k))
   binomial_is_integer |- !n k. k <= n ==> (FACT k * FACT (n - k)) divides (FACT n)
   binomial_pos        |- !n k. k <= n ==> 0 < binomial n k
   binomial_eq_0       |- !n k. (binomial n k = 0) <=> n < k
   binomial_1_n        |- !n. binomial 1 n = if 1 < n then 0 else 1
   binomial_up_eqn     |- !n. 0 < n ==> !k. n * binomial (n - 1) k = (n - k) * binomial n k
   binomial_up         |- !n. 0 < n ==> !k. binomial (n - 1) k = (n - k) * binomial n k DIV n
   binomial_right_eqn  |- !n. 0 < n ==> !k. (k + 1) * binomial n (k + 1) = (n - k) * binomial n k
   binomial_right      |- !n. 0 < n ==> !k. binomial n (k + 1) = (n - k) * binomial n k DIV (k + 1)
   binomial_monotone   |- !n k. k < HALF n ==> binomial n k < binomial n (k + 1)
   binomial_max        |- !n k. binomial n k <= binomial n (HALF n)
   binomial_iff        |- !f. f = binomial <=>
                              !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\
                                    f (n + 1) (k + 1) = f n k + f n (k + 1)

   Primes and Binomial Coefficients:
   prime_divides_binomials     |- !n.  prime n ==> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_divides_binomials_alt |- !n k. prime n /\ 0 < k /\ k < n ==> n divides binomial n k
   prime_divisor_property      |- !n p. 1 < n /\ p < n /\ prime p /\ p divides n ==> ~(p divides (FACT (n - 1) DIV FACT (n - p)))
   divides_binomials_imp_prime |- !n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n
   prime_iff_divides_binomials |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> n divides (binomial n k)
   prime_iff_divides_binomials_alt
                               |- !n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> binomial n k MOD n = 0

   Binomial Theorem:
   GENLIST_binomial_index_shift |- !n x y. GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n =
                                           GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** SUC k) n
   binomial_index_shift   |- !n x y. (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) o SUC =
                                     (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** SUC k)
   binomial_term_merge_x  |- !n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** SUC (n - k) * y ** k)
   binomial_term_merge_y  |- !n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
                                     (\k. binomial n k * x ** (n - k) * y ** SUC k)
   binomial_thm     |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))
   binomial_thm_alt |- !n x y. (x + y) ** n = SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1))
   binomial_sum     |- !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
   binomial_sum_alt |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n

   Binomial Horizontal List:
   binomial_horizontal_0        |- binomial_horizontal 0 = [1]
   binomial_horizontal_len      |- !n. LENGTH (binomial_horizontal n) = n + 1
   binomial_horizontal_mem      |- !n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)
   binomial_horizontal_mem_iff  |- !n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n
   binomial_horizontal_member   |- !n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)
   binomial_horizontal_element  |- !n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)
   binomial_horizontal_pos      |- !n. EVERY (\x. 0 < x) (binomial_horizontal n)
   binomial_horizontal_pos_alt  |- !n x. MEM x (binomial_horizontal n) ==> 0 < x
   binomial_horizontal_sum      |- !n. SUM (binomial_horizontal n) = 2 ** n
   binomial_horizontal_max      |- !n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)
   binomial_row_max             |- !n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)
   binomial_product_identity    |- !m n k. k <= m /\ m <= n ==>
                          (binomial m k * binomial n m = binomial n k * binomial (n - k) (m - k))
   binomial_middle_upper_bound  |- !n. binomial n (HALF n) <= 4 ** HALF n

   Stirling's Approximation:
   Stirling = (!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
              (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
              (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
              (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)
   binomial_middle_by_stirling  |- Stirling ==>
               !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = 2 ** (n + 1) DIV SQRT (2 * pi * n))

   Useful theorems for Binomial:
   binomial_range_shift  |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                                            (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))
   binomial_mod_zero     |- !n. 0 < n ==> !k. (binomial n k MOD n = 0) <=>
                                          (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)
   binomial_range_shift_alt   |- !n . 0 < n ==> ((!k. 0 < k /\ k < n ==>
            (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))
   binomial_mod_zero_alt  |- !n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)

   Binomial Theorem with prime exponent:
   binomial_thm_prime  |- !p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Binomial Coefficients                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define Binomials:
   C(n,0) = 1
   C(0,k) = 0 if k > 0
   C(n+1,k+1) = C(n,k) + C(n,k+1)
*)
val binomial_def = Define`
    (binomial 0 0 = 1) /\
    (binomial (SUC n) 0 = 1) /\
    (binomial 0 (SUC k) = 0)  /\
    (binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k))
`;

(* Theorem: alternative definition of C(n,k). *)
(* Proof: by binomial_def. *)
Theorem binomial_alt:
  !n k. (binomial n 0 = 1) /\
         (binomial 0 (k + 1) = 0) /\
         (binomial (n + 1) (k + 1) = binomial n k + binomial n (k + 1))
Proof
  rewrite_tac[binomial_def, GSYM ADD1] >>
  (Cases_on `n` >> simp[binomial_def])
QED

(* Basic properties *)

(* Theorem: C(n,k) = 0 if n < k *)
(* Proof:
   By induction on n.
   Base case: C(0,k) = 0 if 0 < k, by definition.
   Step case: assume C(n,k) = 0 if n < k.
   then for SUC n < k,
        C(SUC n, k)
      = C(SUC n, SUC h)   where k = SUC h
      = C(n,h) + C(n,SUC h)  h < SUC h = k
      = 0 + 0             by induction hypothesis
      = 0
*)
val binomial_less_0 = store_thm(
  "binomial_less_0",
  ``!n k. n < k ==> (binomial n k = 0)``,
  Induct_on `n` >-
  metis_tac[binomial_def, num_CASES, NOT_ZERO] >>
  rw[binomial_def] >>
  `?h. k = SUC h` by metis_tac[SUC_NOT, NOT_ZERO, SUC_EXISTS, LESS_TRANS] >>
  metis_tac[binomial_def, LESS_MONO_EQ, LESS_TRANS, LESS_SUC, ADD_0]);

(* Theorem: C(n,0) = 1 *)
(* Proof:
   If n = 0, C(n, 0) = C(0, 0) = 1            by binomial_def
   If n <> 0, n = SUC m, and C(SUC m, 0) = 1  by binomial_def
*)
val binomial_n_0 = store_thm(
  "binomial_n_0",
  ``!n. binomial n 0 = 1``,
  metis_tac[binomial_def, num_CASES]);

(* Theorem: C(n,n) = 1 *)
(* Proof:
   By induction on n.
   Base case: C(0,0) = 1,  true by binomial_def.
   Step case: assume C(n,n) = 1
     C(SUC n, SUC n)
   = C(n,n) + C(n,SUC n)
   = 1 + C(n,SUC n)      by induction hypothesis
   = 1 + 0               by binomial_less_0
   = 1
*)
val binomial_n_n = store_thm(
  "binomial_n_n",
  ``!n. binomial n n = 1``,
  Induct_on `n` >-
  metis_tac[binomial_def] >>
  metis_tac[binomial_def, LESS_SUC, binomial_less_0, ADD_0]);

(* Theorem: binomial 0 n = if n = 0 then 1 else 0 *)
(* Proof:
   If n = 0,
      binomial 0 0 = 1     by binomial_n_0
   If n <> 0, then 0 < n.
      binomial 0 n = 0     by binomial_less_0
*)
val binomial_0_n = store_thm(
  "binomial_0_n",
  ``!n. binomial 0 n = if n = 0 then 1 else 0``,
  rw[binomial_n_0, binomial_less_0]);

(* Theorem: C(n+1,k+1) = C(n,k) + C(n,k+1) *)
(* Proof: by definition. *)
val binomial_recurrence = store_thm(
  "binomial_recurrence",
  ``!n k. binomial (SUC n) (SUC k) = binomial n k + binomial n (SUC k)``,
  rw[binomial_def]);

(* Theorem: C(n+k,k) = (n+k)!/n!k!  *)
(* Proof:
   By induction on k.
   Base case: C(n,0) = n!n! = 1   by binomial_n_0
   Step case: assume C(n+k,k) = (n+k)!/n!k!
   To prove C(n+SUC k, SUC k) = (n+SUC k)!/n!(SUC k)!
      By induction on n.
      Base case: C(SUC k, SUC k) = (SUC k)!/(SUC k)! = 1   by binomial_n_n
      Step case: assume C(n+SUC k, SUC k) = (n +SUC k)!/n!(SUC k)!
      To prove C(SUC n + SUC k, SUC k) = (SUC n + SUC k)!/(SUC n)!(SUC k)!
        C(SUC n + SUC k, SUC k)
      = C(SUC SUC (n+k), SUC k)
      = C(SUC (n+k),k) + C(SUC (n+k), SUC k)
      = C(SUC n + k, k) + C(n + SUC k, SUC k)
      = (SUC n + k)!/(SUC n)!k! + (n + SUC k)!/n!(SUC k)!   by two induction hypothesis
      = ((SUC n + k)!(SUC k) + (n + SUC k)(SUC n))/(SUC n)!(SUC k)!
      = (SUC n + SUC k)!/(SUC n)!(SUC k)!
*)
val binomial_formula = store_thm(
  "binomial_formula",
  ``!n k. binomial (n+k) k * (FACT n * FACT k) = FACT (n+k)``,
  Induct_on `k` >-
  metis_tac[binomial_n_0, FACT, MULT_CLAUSES, ADD_0] >>
  Induct_on `n` >-
  metis_tac[binomial_n_n, FACT, MULT_CLAUSES, ADD_CLAUSES] >>
  `SUC n + SUC k = SUC (SUC (n+k))` by decide_tac >>
  `SUC (n + k) = SUC n + k` by decide_tac >>
  `binomial (SUC n + SUC k) (SUC k) * (FACT (SUC n) * FACT (SUC k)) =
    (binomial (SUC (n + k)) k +
     binomial (SUC (n + k)) (SUC k)) * (FACT (SUC n) * FACT (SUC k))`
    by metis_tac[binomial_recurrence] >>
  `_ = binomial (SUC (n + k)) k * (FACT (SUC n) * FACT (SUC k)) +
        binomial (SUC (n + k)) (SUC k) * (FACT (SUC n) * FACT (SUC k))`
        by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = binomial (SUC n + k) k * (FACT (SUC n) * ((SUC k) * FACT k)) +
        binomial (n + SUC k) (SUC k) * ((SUC n) * FACT n * FACT (SUC k))`
        by metis_tac[ADD_COMM, SUC_ADD_SYM, FACT] >>
  `_ = binomial (SUC n + k) k * FACT (SUC n) * FACT k * (SUC k) +
        binomial (n + SUC k) (SUC k) * FACT n * FACT (SUC k) * (SUC n)`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC n + k) * SUC k + FACT (n + SUC k) * SUC n`
        by metis_tac[MULT_COMM, MULT_ASSOC] >>
  `_ = FACT (SUC (n+k)) * SUC k + FACT (SUC (n+k)) * SUC n`
        by metis_tac[ADD_COMM, SUC_ADD_SYM] >>
  `_ = FACT (SUC (n+k)) * (SUC k + SUC n)` by metis_tac[LEFT_ADD_DISTRIB] >>
  `_ = (SUC n + SUC k) * FACT (SUC (n+k))` by metis_tac[MULT_COMM, ADD_COMM] >>
  metis_tac[FACT]);

(* Theorem: C(n,k) = n!/k!(n-k)!  for 0 <= k <= n *)
(* Proof:
     FACT n
   = FACT ((n-k)+k)                                 by SUB_ADD, k <= n.
   = binomial ((n-k)+k) k * (FACT (n-k) * FACT k)   by binomial_formula
   = binomial n k * (FACT (n-k) * FACT k))          by SUB_ADD, k <= n.
*)
val binomial_formula2 = store_thm(
  "binomial_formula2",
  ``!n k. k <= n ==> (FACT n = binomial n k * (FACT (n-k) * FACT k))``,
  metis_tac[binomial_formula, SUB_ADD]);

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))) *)
(* Proof:
    binomial n k
  = (binomial n k * (FACT (n - k) * FACT k)) DIV ((FACT (n - k) * FACT k))  by MULT_DIV
  = (FACT n) DIV ((FACT (n - k) * FACT k))      by binomial_formula2
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by MULT_COMM
*)
val binomial_formula3 = store_thm(
  "binomial_formula3",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV ((FACT k) * (FACT (n - k))))``,
  metis_tac[binomial_formula2, MULT_COMM, MULT_DIV, MULT_EQ_0, FACT_LESS, NOT_ZERO]);

(* Theorem alias. *)
val binomial_fact = save_thm("binomial_fact", binomial_formula3);
(* val binomial_fact = |- !n k. k <= n ==> (binomial n k = FACT n DIV (FACT k * FACT (n - k))): thm *)

(* Theorem: k <= n ==> binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)) *)
(* Proof:
    binomial n k
  = (FACT n) DIV ((FACT k * FACT (n - k)))      by binomial_formula3
  = (FACT n) DIV (FACT k) DIV (FACT (n - k))    by DIV_DIV_DIV_MULT
*)
val binomial_n_k = store_thm(
  "binomial_n_k",
  ``!n k. k <= n ==> (binomial n k = (FACT n) DIV (FACT k) DIV (FACT (n - k)))``,
  metis_tac[DIV_DIV_DIV_MULT, binomial_formula3, MULT_EQ_0, FACT_LESS, NOT_ZERO]);

(* Theorem: binomial n 1 = n *)
(* Proof:
   If n = 0,
        binomial 0 1
      = if 1 = 0 then 1 else 0                by binomial_0_n
      = 0                                     by 1 = 0 = F
   If n <> 0, then 0 < n.
      Thus 1 <= n, and n = SUC (n-1)          by 0 < n
        binomial n 1
      = FACT n DIV FACT 1 DIV FACT (n - 1)    by binomial_n_k, 1 <= n
      = FACT n DIV 1 DIV (FACT (n-1))         by FACT, ONE
      = FACT n DIV (FACT (n-1))               by DIV_1
      = (n * FACT (n-1)) DIV (FACT (n-1))     by FACT
      = n                                     by MULT_DIV, FACT_LESS
*)
val binomial_n_1 = store_thm(
  "binomial_n_1",
  ``!n. binomial n 1 = n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  `1 <= n /\ (n = SUC (n-1))` by decide_tac >>
  `binomial n 1 = FACT n DIV FACT 1 DIV FACT (n - 1)` by rw[binomial_n_k] >>
  `_ = FACT n DIV 1 DIV (FACT (n-1))` by EVAL_TAC >>
  `_ = FACT n DIV (FACT (n-1))` by rw[] >>
  `_ = (n * FACT (n-1)) DIV (FACT (n-1))` by metis_tac[FACT] >>
  `_ = n` by rw[MULT_DIV, FACT_LESS] >>
  rw[]);

(* Theorem: k <= n ==> (binomial n k = binomial n (n-k)) *)
(* Proof:
   Note (n-k) <= n always.
     binomial n k
   = (FACT n) DIV (FACT k * FACT (n - k))           by binomial_formula3, k <= n.
   = (FACT n) DIV (FACT (n - k) * FACT k)           by MULT_COMM
   = (FACT n) DIV (FACT (n - k) * FACT (n-(n-k)))   by n - (n-k) = k
   = binomial n (n-k)                               by binomial_formula3, (n-k) <= n.
*)
val binomial_sym = store_thm(
  "binomial_sym",
  ``!n k. k <= n ==> (binomial n k = binomial n (n-k))``,
  rpt strip_tac >>
  `n - (n-k) = k` by decide_tac >>
  `(n-k) <= n` by decide_tac >>
  rw[binomial_formula3, MULT_COMM]);

(* Theorem: k <= n ==> (FACT k * FACT (n-k)) divides (FACT n) *)
(* Proof:
   Since FACT n = binomial n k * (FACT (n - k) * FACT k)   by binomial_formula2
                = binomial n k * (FACT k * FACT (n - k))   by MULT_COMM
   Hence (FACT k * FACT (n-k)) divides (FACT n)            by divides_def
*)
val binomial_is_integer = store_thm(
  "binomial_is_integer",
  ``!n k. k <= n ==> (FACT k * FACT (n-k)) divides (FACT n)``,
  metis_tac[binomial_formula2, MULT_COMM, divides_def]);

(* Theorem: k <= n ==> 0 < binomial n k *)
(* Proof:
   Since  FACT n = binomial n k * (FACT (n - k) * FACT k)  by binomial_formula2
     and  0 < FACT n, 0 < FACT (n-k), 0 < FACT k           by FACT_LESS
   Hence  0 < binomial n k                                 by ZERO_LESS_MULT
*)
val binomial_pos = store_thm(
  "binomial_pos",
  ``!n k. k <= n ==> 0 < binomial n k``,
  metis_tac[binomial_formula2, FACT_LESS, ZERO_LESS_MULT]);

(* Theorem: (binomial n k = 0) <=> n < k *)
(* Proof:
   If part: (binomial n k = 0) ==> n < k
      By contradiction, suppose k <= n.
      Then 0 < binomial n k                by binomial_pos
      This contradicts binomial n k = 0    by NOT_ZERO
   Only-if part: n < k ==> (binomial n k = 0)
      This is true                         by binomial_less_0
*)
val binomial_eq_0 = store_thm(
  "binomial_eq_0",
  ``!n k. (binomial n k = 0) <=> n < k``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `k <= n` by decide_tac >>
    metis_tac[binomial_pos, NOT_ZERO],
    rw[binomial_less_0]
  ]);

(* Theorem: binomial 1 n = if 1 < n then 0 else 1 *)
(* Proof:
   If n = 0, binomial 1 0 = 1     by binomial_n_0
   If n = 1, binomial 1 1 = 1     by binomial_n_1
   Otherwise, binomial 1 n = 0    by binomial_eq_0, 1 < n
*)
Theorem binomial_1_n:
  !n. binomial 1 n = if 1 < n then 0 else 1
Proof
  rw[binomial_eq_0] >>
  `n = 0 \/ n = 1` by decide_tac >-
  simp[binomial_n_0] >>
  simp[binomial_n_1]
QED

(* Relating Binomial to its up-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial (n-1) k = (n-1, k, n-1-k) = (n-1)! / k! (n-1-k)!
                    = (n!/n) / k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / n
*)

(* Theorem: 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k) *)
(* Proof:
   If n <= k, that is n-1 < k.
      So   binomial (n-1) k = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k <= n-1
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = n * FACT (n-1)                                     by FACT
             = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))   by binomial_formula2, k <= n-1.
             = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             n * binomial (n-1) k = (n-k) * (binomial n k)        by MULT_RIGHT_CANCEL
*)
val binomial_up_eqn = store_thm(
  "binomial_up_eqn",
  ``!n. 0 < n ==> !k. n * binomial (n-1) k = (n-k) * (binomial n k)``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n-1 < k /\ (n - k = 0)` by decide_tac >>
    `binomial (n - 1) k = 0` by rw[binomial_less_0] >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k <= n-1` by decide_tac >>
    `SUC (n-1) = n` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = n * FACT (n-1)` by metis_tac[FACT] >>
    `_ = n * (binomial (n-1) k * (FACT (n-1-k) * FACT k))` by rw_tac std_ss[GSYM binomial_formula2] >>
    `_ = (n * binomial (n-1) k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n *)
(* Proof:
   Since  n * binomial (n-1) k = (n-k) * (binomial n k)        by binomial_up_eqn
              binomial (n-1) k = (n-k) * (binomial n k) DIV n  by DIV_SOLVE, 0 < n.
*)
val binomial_up = store_thm(
  "binomial_up",
  ``!n. 0 < n ==> !k. binomial (n-1) k = ((n-k) * (binomial n k)) DIV n``,
  rw[binomial_up_eqn, DIV_SOLVE]);

(* Relating Binomial to its right-entry:

   binomial n k = (n, k, n-k) = n! / k! (n-k)!
   binomial n (k+1) = (n, k+1, n-k-1) = n! / (k+1)! (n-k-1)!
                    = n! / (k+1) * k! ((n-k)!/(n-k))
                    = (n-k) * binomial n k / (k+1)
*)

(* Theorem: 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k *)
(* Proof:
   If n <= k, that is n < k+1.
      So   binomial n (k+1) = 0      by binomial_less_0
      and  n - k = 0                 by arithmetic
      Hence true                     by MULT_EQ_0
   Otherwise k < n,
      or k <= n, 1 <= n-k, k+1 <= n
      Therefore,
      FACT n = binomial n k * (FACT (n - k) * FACT k)             by binomial_formula2, k <= n.
             = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)   by FACT
             = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)   by MULT_ASSOC
             = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)   by MULT_COMM
      FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))      by binomial_formula2, k+1 <= n.
             = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))        by SUB_PLUS, ADD_COMM
             = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))  by FACT
             = binomial n (k+1) * ((k+1) * (FACT (n-1-k) * FACT k))  by MULT_ASSOC, MULT_COMM
             = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)    by MULT_COMM, MULT_ASSOC
      Since  0 < FACT (n-1-k) * FACT k                            by FACT_LESS, MULT_EQ_0
             (k+1) * binomial n (k+1) = (n-k) * (binomial n k)    by MULT_RIGHT_CANCEL
*)
val binomial_right_eqn = store_thm(
  "binomial_right_eqn",
  ``!n. 0 < n ==> !k. (k + 1) * binomial n (k+1) = (n - k) * binomial n k``,
  rpt strip_tac >>
  `!n. n <> 0 <=> 0 < n` by decide_tac >>
  Cases_on `n <= k` >| [
    `n < k+1` by decide_tac >>
    `binomial n (k+1) = 0` by rw[binomial_less_0] >>
    `n - k = 0` by decide_tac >>
    metis_tac[MULT_EQ_0],
    `k < n /\ k <= n /\ 1 <= n-k /\ k+1 <= n` by decide_tac >>
    `SUC k = k + 1` by decide_tac >>
    `SUC (n-1-k) = n - k` by metis_tac[SUB_PLUS, ADD_COMM, ADD1, SUB_ADD] >>
    `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
    `_ = binomial n k * ((n - k) * FACT (n-1-k) * FACT k)` by metis_tac[FACT] >>
    `_ = binomial n k * (n - k) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (n - k) * binomial n k * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `FACT n = binomial n (k+1) * (FACT (n-(k+1)) * FACT (k+1))` by rw[binomial_formula2] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * FACT (k+1))` by metis_tac[SUB_PLUS, ADD_COMM] >>
    `_ = binomial n (k+1) * (FACT (n-1-k) * ((k+1) * FACT k))` by metis_tac[FACT] >>
    `_ = binomial n (k+1) * ((FACT (n-1-k) * (k+1)) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = binomial n (k+1) * ((k+1) * (FACT (n-1-k)) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    `_ = (binomial n (k+1) * (k+1)) * (FACT (n-1-k) * FACT k)` by rw[MULT_ASSOC] >>
    `_ = (k+1) * binomial n (k+1) * (FACT (n-1-k) * FACT k)` by rw_tac std_ss[MULT_COMM] >>
    metis_tac[FACT_LESS, MULT_EQ_0, MULT_RIGHT_CANCEL]
  ]);

(* Theorem: 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1) *)
(* Proof:
   Since  (k + 1) * binomial n (k+1) = (n - k) * binomial n k  by binomial_right_eqn
          binomial n (k+1) = (n - k) * binomial n k DIV (k+1)  by DIV_SOLVE, 0 < k+1.
*)
val binomial_right = store_thm(
  "binomial_right",
  ``!n. 0 < n ==> !k. binomial n (k+1) = (n - k) * binomial n k DIV (k+1)``,
  rw[binomial_right_eqn, DIV_SOLVE, DECIDE ``!k. 0 < k+1``]);

(*
       k < HALF n <=> k + 1 <= n - k
n = 5, HALF n = 2, binomial 5 k: 1, 5, 10, 10, 5, 1
                              k= 0, 1,  2,  3, 4, 5
       k < 2      <=> k + 1 <= 5 - k
       k = 0              1 <= 5   binomial 5 1 >= binomial 5 0
       k = 1              2 <= 4   binomial 5 2 >= binomial 5 1
n = 6, HALF n = 3, binomial 6 k: 1, 6, 15, 20, 15, 6, 1
                              k= 0, 1, 2,  3,  4,  5, 6
       k < 3      <=> k + 1 <= 6 - k
       k = 0              1 <= 6   binomial 6 1 >= binomial 6 0
       k = 1              2 <= 5   binomial 6 2 >= binomial 6 1
       k = 2              3 <= 4   binomial 6 3 >= binomial 6 2
*)

(* Theorem: k < HALF n ==> binomial n k < binomial n (k + 1) *)
(* Proof:
   Note k < HALF n ==> 0 < n               by ZERO_DIV, 0 < 2
   also k < HALF n ==> k + 1 < n - k       by LESS_HALF_IFF
     so 0 < k + 1 /\ 0 < n - k             by arithmetic
    Now (k + 1) * binomial n (k + 1) = (n - k) * binomial n k   by binomial_right_eqn, 0 < n
   Note HALF n <= n                        by DIV_LESS_EQ, 0 < 2
     so k < HALF n <= n                    by above
   Thus 0 < binomial n k                   by binomial_pos, k <= n
    and 0 < binomial n (k + 1)             by MULT_0, MULT_EQ_0
  Hence binomial n k < binomial n (k + 1)  by MULT_EQ_LESS_TO_MORE
*)
val binomial_monotone = store_thm(
  "binomial_monotone",
  ``!n k. k < HALF n ==> binomial n k < binomial n (k + 1)``,
  rpt strip_tac >>
  `k + 1 < n - k` by rw[GSYM LESS_HALF_IFF] >>
  `0 < k + 1 /\ 0 < n - k` by decide_tac >>
  `(k + 1) * binomial n (k + 1) = (n - k) * binomial n k` by rw[binomial_right_eqn] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `0 < binomial n k` by rw[binomial_pos] >>
  `0 < binomial n (k + 1)` by metis_tac[MULT_0, MULT_EQ_0, NOT_ZERO] >>
  metis_tac[MULT_EQ_LESS_TO_MORE]);

(* Theorem: binomial n k <= binomial n (HALF n) *)
(* Proof:
   Since  (k + 1) * binomial n (k + 1) = (n - k) * binomial n k     by binomial_right_eqn
                    binomial n (k + 1) / binomial n k = (n - k) / (k + 1)
   As k varies from 0, 1,  to (n-1), n
   the ratio varies from n/1, (n-1)/2, (n-2)/3, ...., 1/n, 0/(n+1).
   The ratio is greater than 1 when      (n - k) / (k + 1) > 1
   or  n - k > k + 1
   or      n > 2 * k + 1
   or HALF n >= k + (HALF 1)
   or      k <= HALF n
   Thus (binomial n (HALF n)) is greater than all preceding coefficients.
   For k > HALF n, note that (binomial n k = binomial n (n - k))   by binomial_sym
   Hence (binomial n (HALF n)) is greater than all succeeding coefficients, too.

   If n = 0,
      binomial 0 k = 1 or 0    by binomial_0_n
      binomial 0 (HALF 0) = 1  by binomial_0_n, ZERO_DIV
      Hence true.
   If n <> 0,
      If k = HALF n, trivially true.
      If k < HALF n,
         Then binomial n k < binomial n (HALF n)           by binomial_monotone, MONOTONE_MAX
         Hence true.
      If ~(k < HALF n), HALF n < k.
         Then n - k <= HALF n                              by MORE_HALF_IMP
         If k > n,
            Then binomial n k = 0, hence true              by binomial_less_0
         If ~(k > n), then k <= n.
            Then binomial n k = binomial n (n - k)         by binomial_sym, k <= n
            If n - k = HALF n, trivially true.
            Otherwise, n - k < HALF n,
            Thus binomial n (n - k) < binomial n (HALF n)  by binomial_monotone, MONOTONE_MAX
         Hence true.
*)
val binomial_max = store_thm(
  "binomial_max",
  ``!n k. binomial n k <= binomial n (HALF n)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[binomial_0_n] >>
  Cases_on `k = HALF n` >-
  rw[] >>
  Cases_on `k < HALF n` >| [
    `binomial n k < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac,
    `HALF n < k` by decide_tac >>
    `n - k <= HALF n` by rw[MORE_HALF_IMP] >>
    Cases_on `k > n` >-
    rw[binomial_less_0] >>
    `k <= n` by decide_tac >>
    `binomial n k = binomial n (n - k)` by rw[GSYM binomial_sym] >>
    Cases_on `n - k = HALF n` >-
    rw[] >>
    `n - k < HALF n` by decide_tac >>
    `binomial n (n - k) < binomial n (HALF n)` by rw[binomial_monotone, MONOTONE_MAX] >>
    decide_tac
  ]);

(* Idea: the recurrence relation for binomial defines itself. *)

(* Theorem: f = binomial <=>
            !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\
                  f (n + 1) (k + 1) = f n k + f n (k + 1) *)
(* Proof:
   If part: f = binomial ==> recurrence, true  by binomial_alt
   Only-if part: recurrence ==> f = binomial
   By FUN_EQ_THM, this is to show:
      !n k. f n k = binomial n k
   By double induction, first induct on k.
   Base: !n. f n 0 = binomial n 0, true        by binomial_n_0
   Step: !n. f n k = binomial n k ==>
         !n. f n (SUC k) = binomial n (SUC k)
       By induction on n.
       Base: f 0 (SUC k) = binomial 0 (SUC k)
             This is true                      by binomial_0_n, ADD1
       Step: f n (SUC k) = binomial n (SUC k) ==>
             f (SUC n) (SUC k) = binomial (SUC n) (SUC k)

             f (SUC n) (SUC k)
           = f (n + 1) (k + 1)                 by ADD1
           = f n k + f n (k + 1)               by given
           = binomial n k + binomial n (k + 1) by induction hypothesis
           = binomial (n + 1) (k + 1)          by binomial_alt
           = binomial (SUC n) (SUC k)          by ADD1
*)
Theorem binomial_iff:
  !f. f = binomial <=>
      !n k. f n 0 = 1 /\ f 0 (k + 1) = 0 /\ f (n + 1) (k + 1) = f n k + f n (k + 1)
Proof
  rw[binomial_alt, EQ_IMP_THM] >>
  simp[FUN_EQ_THM] >>
  Induct_on `x'` >-
  simp[binomial_n_0] >>
  Induct_on `x` >-
  fs[binomial_0_n, ADD1] >>
  fs[binomial_alt, ADD1]
QED

(* ------------------------------------------------------------------------- *)
(* Primes and Binomial Coefficients                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   C(n,k) = n!/k!/(n-k)!
   or n! = C(n,k) k! (n-k)!
   n divides n!, so n divides the product C(n,k) k!(n-k)!
   For a prime n, n cannot divide k!(n-k)!, all factors less than prime n.
   By Euclid's lemma, a prime divides a product must divide a factor.
   So p divides C(n,k).
*)
val prime_divides_binomials = store_thm(
  "prime_divides_binomials",
  ``!n. prime n ==> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  rpt strip_tac >-
  metis_tac[ONE_LT_PRIME] >>
  `(n = n-k + k) /\ (n-k) < n` by decide_tac >>
  `FACT n = (binomial n k) * (FACT (n-k) * FACT k)` by metis_tac[binomial_formula] >>
  `~(n divides (FACT k)) /\ ~(n divides (FACT (n-k)))` by metis_tac[PRIME_BIG_NOT_DIVIDES_FACT] >>
  `n divides (FACT n)` by metis_tac[DIVIDES_FACT, LESS_TRANS] >>
  metis_tac[P_EUCLIDES]);

(* Theorem: n is prime ==> n divides C(n,k)  for all 0 < k < n *)
(* Proof: by prime_divides_binomials *)
val prime_divides_binomials_alt = store_thm(
  "prime_divides_binomials_alt",
  ``!n k. prime n /\ 0 < k /\ k < n ==> n divides (binomial n k)``,
  rw[prime_divides_binomials]);

(* Theorem: If prime p divides n, p does not divide (n-1)!/(n-p)! *)
(* Proof:
   By contradiction.
   (n-1)...(n-p+1)/p  cannot be an integer
   as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val prime_divisor_property = store_thm(
  "prime_divisor_property",
  ``!n p. 1 < n /\ p < n /\ prime p /\ p divides n ==>
   ~(p divides ((FACT (n-1)) DIV (FACT (n-p))))``,
  spose_not_then strip_assume_tac >>
  `1 < p` by metis_tac[ONE_LT_PRIME] >>
  `n-p < n-1` by decide_tac >>
  `(FACT (n-1)) DIV (FACT (n-p)) = PROD_SET (IMAGE SUC ((count (n-1)) DIFF (count (n-p))))`
   by metis_tac[FACT_REDUCTION, MULT_DIV, FACT_LESS] >>
  `(count (n-1)) DIFF (count (n-p)) = {x | (n-p) <= x /\ x < (n-1)}`
   by srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  `IMAGE SUC {x | (n-p) <= x /\ x < (n-1)} = {x | (n-p) < x /\ x < n}` by
  (srw_tac[ARITH_ss][EXTENSION, EQ_IMP_THM] >>
  qexists_tac `x-1` >>
  decide_tac) >>
  `FINITE (count (n - 1) DIFF count (n - p))` by rw[] >>
  `?y. y IN {x| n - p < x /\ x < n} /\ p divides y` by metis_tac[PROD_SET_EUCLID, IMAGE_FINITE] >>
  `!m n y. y IN {x | m < x /\ x < n} ==> m < y /\ y < n` by rw[] >>
  `n-p < y /\ y < n` by metis_tac[] >>
  `y < n + p` by decide_tac >>
  `y = n` by metis_tac[MULTIPLE_INTERVAL] >>
  decide_tac);

(* Theorem: n divides C(n,k)  for all 0 < k < n ==> n is prime *)
(* Proof:
   By contradiction. Let p be a proper factor of n, 1 < p < n.
   Then C(n,p) = n(n-1)...(n-p+1)/p(p-1)..1
   is divisible by n/p, but not n, since
   C(n,p)/n = (n-1)...(n-p+1)/p(p-1)...1
   cannot be an integer as p cannot divide any of the numerator.
   Note: when p divides n, the nearest multiples for p are n+/-p.
*)
val divides_binomials_imp_prime = store_thm(
  "divides_binomials_imp_prime",
  ``!n. 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k)) ==> prime n``,
  (spose_not_then strip_assume_tac) >>
  `?p. prime p /\ p < n /\ p divides n` by metis_tac[PRIME_FACTOR_PROPER] >>
  `n divides (binomial n p)` by metis_tac[PRIME_POS] >>
  `0 < p` by metis_tac[PRIME_POS] >>
  `(n = n-p + p) /\ (n-p) < n` by decide_tac >>
  `FACT n = (binomial n p) * (FACT (n-p) * FACT p)` by metis_tac[binomial_formula] >>
  `(n = SUC (n-1)) /\ (p = SUC (p-1))` by decide_tac >>
  `(FACT n = n * FACT (n-1)) /\ (FACT p = p * FACT (p-1))` by metis_tac[FACT] >>
  `n * FACT (n-1) = (binomial n p) * (FACT (n-p) * (p * FACT (p-1)))` by metis_tac[] >>
  `0 < n` by decide_tac >>
  `?q. binomial n p = n * q` by metis_tac[divides_def, MULT_COMM] >>
  `0 <> n` by decide_tac >>
  `FACT (n-1) = q * (FACT (n-p) * (p * FACT (p-1)))`
    by metis_tac[EQ_MULT_LCANCEL, MULT_ASSOC] >>
  `_ = q * ((FACT (p-1) * p)* FACT (n-p))` by metis_tac[MULT_COMM] >>
  `_ = q * FACT (p-1) * p * FACT (n-p)` by metis_tac[MULT_ASSOC] >>
  `FACT (n-1) DIV FACT (n-p) = q * FACT (p-1) * p` by metis_tac[MULT_DIV, FACT_LESS] >>
  metis_tac[divides_def, prime_divisor_property]);

(* Theorem: n is prime iff n divides C(n,k)  for all 0 < k < n *)
(* Proof:
   By prime_divides_binomials and
   divides_binomials_imp_prime.
*)
val prime_iff_divides_binomials = store_thm(
  "prime_iff_divides_binomials",
  ``!n. prime n <=> 1 < n /\ (!k. 0 < k /\ k < n ==> n divides (binomial n k))``,
  metis_tac[prime_divides_binomials, divides_binomials_imp_prime]);

(* Theorem: prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0) *)
(* Proof: by prime_iff_divides_binomials *)
val prime_iff_divides_binomials_alt = store_thm(
  "prime_iff_divides_binomials_alt",
  ``!n. prime n <=> 1 < n /\ !k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)``,
  rw[prime_iff_divides_binomials, DIVIDES_MOD_0]);

(* ------------------------------------------------------------------------- *)
(* Binomial Theorem                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Binomial Index Shifting, for
     SUM (k=1..n) C(n,k)x^(n+1-k)y^k
   = SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
 *)
(* Proof:
SUM (k=1..n) C(n,k)x^(n+1-k)y^k
= SUM (MAP (\k. (binomial n k)* x**(n+1-k) * y**k) (GENLIST SUC n))
= SUM (GENLIST (\k. (binomial n k)* x**(n+1-k) * y**k) o SUC n)

SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1)
= SUM (MAP (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) (GENLIST I n))
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) o I n)
= SUM (GENLIST (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1)) n)

i.e.

(\k. (binomial n k)* x**(n-k+1) * y**k) o SUC
= (\k. (binomial n (k+1)) * x**(n-k) * y**(k+1))
*)
(* Theorem: Binomial index shift for GENLIST *)
val GENLIST_binomial_index_shift = store_thm(
  "GENLIST_binomial_index_shift",
  ``!n x y. GENLIST ((\k. binomial n k * x ** SUC(n - k) * y ** k) o SUC) n =
           GENLIST (\k. binomial n (SUC k) * x ** (n-k) * y**(SUC k)) n``,
  rw_tac std_ss[GENLIST_FUN_EQ] >>
  `SUC (n - SUC k) = n - k` by decide_tac >>
  rw_tac std_ss[]);

(* This is closely related to above, with (SUC n) replacing (n),
   but does not require k < n. *)
(* Proof: by function equality. *)
val binomial_index_shift = store_thm(
  "binomial_index_shift",
  ``!n x y. (\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC =
           (\k. binomial (SUC n) (SUC k) * x ** (n-k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM]);

(* Pattern for binomial expansion:

    (x+y)(x^3 + 3x^2y + 3xy^2 + y^3)
    = x(x^3) + 3x(x^2y) + 3x(xy^2) + x(y^3) +
                 y(x^3) + 3y(x^2y) + 3y(xy^2) + y(y^3)
    = x^4 + (3+1)x^3y + (3+3)(x^2y^2) + (1+3)(xy^3) + y^4
    = x^4 + 4x^3y     + 6x^2y^2       + 4xy^3       + y^4

*)

(* Theorem: multiply x into a binomial term *)
(* Proof: by function equality and EXP. *)
val binomial_term_merge_x = store_thm(
  "binomial_term_merge_x",
  ``!n x y. (\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (SUC(n - k)) * y ** k)``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `x * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * (x * x ** (n - k)) * y ** k` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: multiply y into a binomial term *)
(* Proof: by functional equality and EXP. *)
val binomial_term_merge_y = store_thm(
  "binomial_term_merge_y",
  ``!n x y. (\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k) =
           (\k. binomial n k * x ** (n - k) * y ** (SUC k))``,
  rw_tac std_ss[FUN_EQ_THM] >>
  `y * (binomial n k * x ** (n - k) * y ** k) =
    binomial n k * x ** (n - k) * (y * y ** k)` by decide_tac >>
  metis_tac[EXP]);

(* Theorem: [Binomial Theorem]  (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k  *)
(* Proof:
   By induction on n.
   Base case: to prove (x + y)^0 = SUM (k=0..0) C(0,k)x^(0-k)y^k
   (x + y)^0 = 1    by EXP
   SUM (k=0..0) C(0,k)x^(n-k)y^k = C(0,0)x^(0-0)y^0 = C(0,0) = 1  by EXP, binomial_def
   Step case: assume (x + y)^n = SUM (k=0..n) C(n,k)x^(n-k)y^k
    to prove: (x + y)^SUC n = SUM (k=0..(SUC n)) C(SUC n,k)x^((SUC n)-k)y^k
      (x + y)^SUC n
    = (x + y)(x + y)^n      by EXP
    = (x + y) SUM (k=0..n) C(n,k)x^(n-k)y^k   by induction hypothesis
    = x (SUM (k=0..n) C(n,k)x^(n-k)y^k) +
      y (SUM (k=0..n) C(n,k)x^(n-k)y^k)       by RIGHT_ADD_DISTRIB
    = SUM (k=0..n) C(n,k)x^(n+1-k)y^k +
      SUM (k=0..n) C(n,k)x^(n-k)y^(k+1)       by moving factor into SUM
    = C(n,0)x^(n+1) + SUM (k=1..n) C(n,k)x^(n+1-k)y^k +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by breaking sum

    = C(n,0)x^(n+1) + SUM (k=0..n-1) C(n,k+1)x^(n-k)y^(k+1) +
                      SUM (k=0..n-1) C(n,k)x^(n-k)y^(k+1) + C(n,n)y^(n+1)
                                              by index shifting
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) [C(n,k+1) + C(n,k)] x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by merging sums
    = C(n,0)x^(n+1) +
      SUM (k=0..n-1) C(n+1,k+1) x^(n-k)y^(k+1) +
      C(n,n)y^(n+1)                           by binomial recurrence
    = C(n,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n,n)y^(n+1)                           by index shifting again
    = C(n+1,0)x^(n+1) +
      SUM (k=1..n) C(n+1,k) x^(n+1-k)y^k +
      C(n+1,n+1)y^(n+1)                       by binomial identities
    = SUM (k=0..(SUC n))C(SUC n,k) x^((SUC n)-k)y^k
                                              by synthesis of sum
*)
val binomial_thm = store_thm(
  "binomial_thm",
  ``!n x y. (x + y) ** n = SUM (GENLIST (\k. (binomial n k) * x ** (n-k) * y ** k) (SUC n))``,
  Induct_on `n` >-
  rw[EXP, binomial_n_n] >>
  rw_tac std_ss[EXP] >>
  `(x + y) * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) =
    x * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n)) +
    y * SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (SUC n))`
    by metis_tac[RIGHT_ADD_DISTRIB] >>
  `_ = SUM (GENLIST ((\k. x * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n)) +
        SUM (GENLIST ((\k. y * k) o (\k. binomial n k * x ** (n - k) * y ** k)) (SUC n))`
    by metis_tac[SUM_MULT, MAP_GENLIST] >>
  `_ = SUM (GENLIST (\k. binomial n k * x ** SUC(n - k) * y ** k) (SUC n)) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[binomial_term_merge_x, binomial_term_merge_y] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) (SUC n))`
    by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
         SUM (GENLIST ((\k. binomial n k * x ** SUC (n - k) * y ** k) o SUC) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by rw[SUM_DECOMPOSE_LAST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
         SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n )`
    by metis_tac[GENLIST_binomial_index_shift] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        (SUM (GENLIST (\k. binomial n (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
         SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n)) +
         (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by decide_tac >>
  `_ = (\k. binomial n k * x ** SUC (n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) * x ** (n - k) * y ** (SUC k) +
                           binomial n k * x ** (n - k) * y ** (SUC k))) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by metis_tac[SUM_ADD_GENLIST] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. (binomial n (SUC k) + binomial n k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[RIGHT_ADD_DISTRIB, MULT_ASSOC] >>
  `_ = (\k. binomial n k * x ** SUC(n - k) * y ** k) 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        (\k. binomial n k * x ** (n - k) * y ** (SUC k)) n`
    by rw[binomial_recurrence, ADD_COMM] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST (\k. binomial (SUC n) (SUC k) * x ** (n - k) * y ** (SUC k)) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_n_0, binomial_n_n] >>
  `_ = binomial (SUC n) 0 * x ** (SUC n) * y ** 0 +
        SUM (GENLIST ((\k. binomial (SUC n) k * x ** ((SUC n) - k) * y ** k) o SUC) n) +
        binomial (SUC n) (SUC n) * x ** 0 * y ** (SUC n)`
        by rw[binomial_index_shift] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)) +
        (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC n)`
        by rw[SUM_DECOMPOSE_FIRST] >>
  `_ = SUM (GENLIST (\k. binomial (SUC n) k * x ** (SUC n - k) * y ** k) (SUC (SUC n)))`
        by rw[SUM_DECOMPOSE_LAST] >>
  decide_tac);

(* This is a milestone theorem. *)

(* Derive an alternative form. *)
val binomial_thm_alt = save_thm("binomial_thm_alt",
    binomial_thm |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_thm_alt =
   |- !n x y. (x + y) ** n =
              SUM (GENLIST (\k. binomial n k * x ** (n - k) * y ** k) (n + 1)): thm *)

(* Theorem: SUM (GENLIST (binomial n) (SUC n)) = 2 ** n *)
(* Proof: by binomial_sum_alt and function equality. *)
(* Proof:
   Put x = 1, y = 1 in binomial_thm,
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))
   (1 + 1) ** n = SUM (GENLIST (\k. binomial n k) (SUC n))    by EXP_1
   or    2 ** n = SUM (GENLIST (binomial n) (SUC n))          by FUN_EQ_THM
*)
Theorem binomial_sum:
  !n. SUM (GENLIST (binomial n) (SUC n)) = 2 ** n
Proof
  rpt strip_tac >>
  `!n. (\k. binomial n k * 1 ** (n - k) * 1 ** k) = binomial n` by rw[FUN_EQ_THM] >>
  `SUM (GENLIST (binomial n) (SUC n)) =
    SUM (GENLIST (\k. binomial n k * 1 ** (n - k) * 1 ** k) (SUC n))` by fs[] >>
  `_ = (1 + 1) ** n` by rw[GSYM binomial_thm] >>
  simp[]
QED

(* Derive an alternative form. *)
val binomial_sum_alt = save_thm("binomial_sum_alt",
    binomial_sum |> SIMP_RULE bool_ss [ADD1]);
(* val binomial_sum_alt = |- !n. SUM (GENLIST (binomial n) (n + 1)) = 2 ** n: thm *)

(* ------------------------------------------------------------------------- *)
(* Binomial Horizontal List                                                  *)
(* ------------------------------------------------------------------------- *)

(* Define Horizontal List in Pascal Triangle *)
(*
val binomial_horizontal_def = Define `
  binomial_horizontal n = GENLIST (binomial n) (SUC n)
`;
*)

(* Use overloading for binomial_horizontal n. *)
val _ = overload_on("binomial_horizontal", ``\n. GENLIST (binomial n) (n + 1)``);

(* Theorem: binomial_horizontal 0 = [1] *)
(* Proof:
     binomial_horizontal 0
   = GENLIST (binomial 0) (0 + 1)    by notation
   = SNOC (binomial 0 0) []          by GENLIST, ONE
   = [binomial 0 0]                  by SNOC
   = [1]                             by binomial_n_0
*)
val binomial_horizontal_0 = store_thm(
  "binomial_horizontal_0",
  ``binomial_horizontal 0 = [1]``,
  rw[binomial_n_0]);

(* Theorem: LENGTH (binomial_horizontal n) = n + 1 *)
(* Proof:
     LENGTH (binomial_horizontal n)
   = LENGTH (GENLIST (binomial n) (n + 1)) by notation
   = n + 1                                 by LENGTH_GENLIST
*)
val binomial_horizontal_len = store_thm(
  "binomial_horizontal_len",
  ``!n. LENGTH (binomial_horizontal n) = n + 1``,
  rw[]);

(* Theorem: k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n) *)
(* Proof: by MEM_GENLIST *)
val binomial_horizontal_mem = store_thm(
  "binomial_horizontal_mem",
  ``!n k. k < n + 1 ==> MEM (binomial n k) (binomial_horizontal n)``,
  metis_tac[MEM_GENLIST]);

(* Theorem: MEM (binomial n k) (binomial_horizontal n) <=> k <= n *)
(* Proof:
   If part: MEM (binomial n k) (binomial_horizontal n) ==> k <= n
      By contradiction, suppose n < k.
      Then binomial n k = 0        by binomial_less_0, ~(k <= n)
       But ?m. m < n + 1 ==> 0 = binomial n m    by MEM_GENLIST
        or m <= n ==> binomial n m = 0           by m < n + 1
       Yet binomial n m <> 0                     by binomial_eq_0
      This is a contradiction.
   Only-if part: k <= n ==> MEM (binomial n k) (binomial_horizontal n)
      By MEM_GENLIST, this is to show:
           ?m. m < n + 1 /\ (binomial n k = binomial n m)
      Note k <= n ==> k < n + 1,
      Take m = k, the result follows.
*)
val binomial_horizontal_mem_iff = store_thm(
  "binomial_horizontal_mem_iff",
  ``!n k. MEM (binomial n k) (binomial_horizontal n) <=> k <= n``,
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `binomial n k = 0` by rw[binomial_less_0] >>
    fs[MEM_GENLIST] >>
    `m <= n` by decide_tac >>
    fs[binomial_eq_0],
    rw[MEM_GENLIST] >>
    `k < n + 1` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k) *)
(* Proof:
   By MEM_GENLIST, this is to show:
      (?m. m < n + 1 /\ (x = binomial n m)) <=> ?k. k <= n /\ (x = binomial n k)
   Since m < n + 1 <=> m <= n              by LE_LT1
   This is trivially true.
*)
val binomial_horizontal_member = store_thm(
  "binomial_horizontal_member",
  ``!n x. MEM x (binomial_horizontal n) <=> ?k. k <= n /\ (x = binomial n k)``,
  metis_tac[MEM_GENLIST, LE_LT1]);

(* Theorem: k <= n ==> (EL k (binomial_horizontal n) = binomial n k) *)
(* Proof: by EL_GENLIST *)
val binomial_horizontal_element = store_thm(
  "binomial_horizontal_element",
  ``!n k. k <= n ==> (EL k (binomial_horizontal n) = binomial n k)``,
  rw[EL_GENLIST]);

(* Theorem: EVERY (\x. 0 < x) (binomial_horizontal n) *)
(* Proof:
       EVERY (\x. 0 < x) (binomial_horizontal n)
   <=> EVERY (\x. 0 < x) (GENLIST (binomial n) (n + 1)) by notation
   <=> !k. k < n + 1 ==>  0 < binomial n k              by EVERY_GENLIST
   <=> !k. k <= n ==> 0 < binomial n k                  by arithmetic
   <=> T                                                by binomial_pos
*)
val binomial_horizontal_pos = store_thm(
  "binomial_horizontal_pos",
  ``!n. EVERY (\x. 0 < x) (binomial_horizontal n)``,
  rpt strip_tac >>
  `!k n. k < n + 1 <=> k <= n` by decide_tac >>
  rw_tac std_ss[EVERY_GENLIST, LESS_EQ_IFF_LESS_SUC, binomial_pos]);

(* Theorem: MEM x (binomial_horizontal n) ==> 0 < x *)
(* Proof: by binomial_horizontal_pos, EVERY_MEM *)
val binomial_horizontal_pos_alt = store_thm(
  "binomial_horizontal_pos_alt",
  ``!n x. MEM x (binomial_horizontal n) ==> 0 < x``,
  metis_tac[binomial_horizontal_pos, EVERY_MEM]);

(* Theorem: SUM (binomial_horizontal n) = 2 ** n *)
(* Proof:
     SUM (binomial_horizontal n)
   = SUM (GENLIST (binomial n) (n + 1))   by notation
   = 2 ** n                               by binomial_sum, ADD1
*)
val binomial_horizontal_sum = store_thm(
  "binomial_horizontal_sum",
  ``!n. SUM (binomial_horizontal n) = 2 ** n``,
  rw_tac std_ss[binomial_sum, GSYM ADD1]);

(* Theorem: MAX_LIST (binomial_horizontal n) = binomial n (HALF n) *)
(* Proof:
   Let l = binomial_horizontal n, m = binomial n (HALF n).
   Then l <> []                   by binomial_horizontal_len, LENGTH_NIL
    and HALF n <= n               by DIV_LESS_EQ, 0 < 2
     or HALF n < n + 1            by arithmetic
   Also MEM m l                   by binomial_horizontal_mem
    and !x. MEM x l ==> x <= m    by binomial_max, MEM_GENLIST
   Thus m = MAX_LIST l            by MAX_LIST_TEST
*)
val binomial_horizontal_max = store_thm(
  "binomial_horizontal_max",
  ``!n. MAX_LIST (binomial_horizontal n) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `l = binomial_horizontal n` >>
  qabbrev_tac `m = binomial n (HALF n)` >>
  `l <> []` by metis_tac[binomial_horizontal_len, LENGTH_NIL, DECIDE``n + 1 <> 0``] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n < n + 1` by decide_tac >>
  `MEM m l` by rw[binomial_horizontal_mem, Abbr`l`, Abbr`m`] >>
  metis_tac[binomial_max, MEM_GENLIST, MAX_LIST_TEST]);

(* Theorem: MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n) *)
(* Proof:
   Let f = binomial n, s = IMAGE f (count (n + 1)).
   Note FINITE (count (n + 1))      by FINITE_COUNT
     so FINITE s                    by IMAGE_FINITE
   Also count (n + 1) <> {}         by COUNT_EQ_EMPTY, n + 1 <> 0
     so s <> {}                     by IMAGE_EQ_EMPTY
    Now !k. k IN (count (n + 1)) ==> f k <= f (HALF n)   by binomial_max
    ==> !x. x IN s ==> x <= f (HALF n)                   by IN_IMAGE
   Also HALF n <= n                 by DIV_LESS_EQ, 0 < 2
     so HALF n IN (count (n + 1))   by IN_COUNT
    ==> f (HALF n) IN s             by IN_IMAGE
   Thus MAX_SET s = f (HALF n)      by MAX_SET_TEST
*)
val binomial_row_max = store_thm(
  "binomial_row_max",
  ``!n. MAX_SET (IMAGE (binomial n) (count (n + 1))) = binomial n (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `f = binomial n` >>
  qabbrev_tac `s = IMAGE f (count (n + 1))` >>
  `FINITE s` by rw[Abbr`s`] >>
  `s <> {}` by rw[COUNT_EQ_EMPTY, Abbr`s`] >>
  `!k. k IN (count (n + 1)) ==> f k <= f (HALF n)` by rw[binomial_max, Abbr`f`] >>
  `!x. x IN s ==> x <= f (HALF n)` by metis_tac[IN_IMAGE] >>
  `HALF n <= n` by rw[DIV_LESS_EQ] >>
  `HALF n IN (count (n + 1))` by rw[] >>
  `f (HALF n) IN s` by metis_tac[IN_IMAGE] >>
  rw[MAX_SET_TEST]);

(* Theorem: k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k))) *)
(* Proof:
   Using binomial_formula2,

     (binomial m k) * (binomial n m)
         n!            m!
   = ----------- * ------------------      binomial formula
     m! (n - m)!    k! (m - k)!
        n!           m!
   = ----------- * ------------------      cancel m!
      k! m!        (m - k)! (n - m)!
        n!            (n - k)!
   = ----------- * ------------------      replace by (n - k)!
     k! (n - k)!   (m - k)! (n - m)!

   = (binomial n k) * (binomial (n - k) (m - k))   binomial formula
*)
val binomial_product_identity = store_thm(
  "binomial_product_identity",
  ``!m n k. k <= m /\ m <= n ==>
           ((binomial m k) * (binomial n m) = (binomial n k) * (binomial (n - k) (m - k)))``,
  rpt strip_tac >>
  `m - k <= n - k` by decide_tac >>
  `(n - k) - (m - k) = n - m` by decide_tac >>
  `FACT m = binomial m k * (FACT (m - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT n = binomial n m * (FACT (n - m) * FACT m)` by rw[binomial_formula2] >>
  `FACT n = binomial n k * (FACT (n - k) * FACT k)` by rw[binomial_formula2] >>
  `FACT (n - k) = binomial (n - k) (m - k) * (FACT (n - m) * FACT (m - k))` by metis_tac[binomial_formula2] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial m k) * (binomial n m))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  `FACT n = FACT (n - m) * (FACT k * (FACT (m - k) * ((binomial n k) * (binomial (n - k) (m - k)))))` by metis_tac[MULT_ASSOC, MULT_COMM] >>
  metis_tac[MULT_LEFT_CANCEL, FACT_LESS, NOT_ZERO]);

(* Theorem: binomial n (HALF n) <= 4 ** (HALF n) *)
(* Proof:
   Let m = HALF n, l = binomial_horizontal n
   Note LENGTH l = n + 1               by binomial_horizontal_len
   If EVEN n,
      Then n = 2 * m                   by EVEN_HALF
       and m <= n                      by m <= 2 * m
      Note EL m l <= SUM l             by SUM_LE_EL, m < n + 1
       Now EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 4 ** m                      by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
   If ~EVEN n,
      Then ODD n                       by EVEN_ODD
       and n = 2 * m + 1               by ODD_HALF
        so m + 1 <= n                  by m + 1 <= 2 * m + 1
      with m <= n                      by m + 1 <= n
      Note EL m l = binomial n m       by binomial_horizontal_element, m <= n
       and EL (m + 1) l = binomial n (m + 1)  by binomial_horizontal_element, m + 1 <= n
      Note binomial n (m + 1) = binomial n m  by binomial_sym
      Thus 2 * binomial n m
         = binomial n m + binomial n (m + 1)   by above
         = EL m l + EL (m + 1) l
        <= SUM l                       by SUM_LE_SUM_EL, m < m + 1, m + 1 < n + 1
       and SUM l
         = 2 ** n                      by binomial_horizontal_sum
         = 2 * 2 ** (2 * m)            by EXP, ADD1
         = 2 * 4 ** m                  by EXP_EXP_MULT
      Hence binomial n m <= 4 ** m.
*)
val binomial_middle_upper_bound = store_thm(
  "binomial_middle_upper_bound",
  ``!n. binomial n (HALF n) <= 4 ** (HALF n)``,
  rpt strip_tac >>
  qabbrev_tac `m = HALF n` >>
  qabbrev_tac `l = binomial_horizontal n` >>
  `LENGTH l = n + 1` by rw[binomial_horizontal_len, Abbr`l`] >>
  Cases_on `EVEN n` >| [
    `n = 2 * m` by rw[EVEN_HALF, Abbr`m`] >>
    `m < n + 1` by decide_tac >>
    `EL m l <= SUM l` by rw[SUM_LE_EL] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac,
    `ODD n` by metis_tac[EVEN_ODD] >>
    `n = 2 * m + 1` by rw[ODD_HALF, Abbr`m`] >>
    `EL m l = binomial n m` by rw[binomial_horizontal_element, Abbr`l`] >>
    `EL (m + 1) l = binomial n (m + 1)` by rw[binomial_horizontal_element, Abbr`l`] >>
    `binomial n (m + 1) = binomial n m` by rw[Once binomial_sym] >>
    `EL m l + EL (m + 1) l <= SUM l` by rw[SUM_LE_SUM_EL] >>
    `SUM l = 2 ** n` by rw[binomial_horizontal_sum, Abbr`l`] >>
    `_ = 2 * 2 ** (2 * m)` by metis_tac[EXP, ADD1] >>
    `_ = 2 * 4 ** m` by rw[EXP_EXP_MULT] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Stirling's Approximation                                                  *)
(* ------------------------------------------------------------------------- *)

(* Stirling's formula: n! ~ sqrt(2 pi n) (n/e)^n. *)
val _ = overload_on("Stirling",
   ``(!n. FACT n = (SQRT (2 * pi * n)) * (n DIV e) ** n) /\
     (!n. SQRT n = n ** h) /\ (2 * h = 1) /\ (0 < pi) /\ (0 < e) /\
     (!a b x y. (a * b) DIV (x * y) = (a DIV x) * (b DIV y)) /\
     (!a b c. (a DIV c) DIV (b DIV c) = a DIV b)``);

(* Theorem: Stirling ==>
            !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n))) *)
(* Proof:
   Note HALF n <= n                 by DIV_LESS_EQ, 0 < 2
   Let k = HALF n, then n = 2 * k   by EVEN_HALF
   Note 0 < k                       by 0 < n = 2 * k
     so (k * 2) DIV k = 2           by MULT_TO_DIV, 0 < k
     or n DIV k = 2                 by MULT_COMM
   Also 0 < pi * n                  by MULT_EQ_0, 0 < pi, 0 < n
     so 0 < 2 * pi * n              by arithmetic

   Some theorems on the fly:
   Claim: !a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j       [1]
   Proof: By induction on j.
          Base: (a ** 0) DIV (b ** 0) = (a DIV b) ** 0
                (a ** 0) DIV (b ** 0)
              = 1 DIV 1 = 1             by EXP, DIVMOD_ID, 0 < 1
              = (a DIV b) ** 0          by EXP
          Step: (a ** j) DIV (b ** j) = (a DIV b) ** j ==>
                (a ** (SUC j)) DIV (b ** (SUC j)) = (a DIV b) ** (SUC j)
                (a ** (SUC j)) DIV (b ** (SUC j))
              = (a * a ** j) DIV (b * b ** j)        by EXP
              = (a DIV b) * ((a ** j) DIV (b ** j))  by assumption
              = (a DIV b) * (a DIV b) ** j           by induction hypothesis
              = (a DIV b) ** (SUC j)                 by EXP

   Claim: !a b c. (a DIV b) * c = (a * c) DIV b      [2]
   Proof:   (a DIV b) * c
          = (a DIV b) * (c DIV 1)                    by DIV_1
          = (a * c) DIV (b * 1)                      by assumption
          = (a * c) DIV b                            by MULT_RIGHT_1

   Claim: !a b. a DIV b = 2 * (a DIV (2 * b))        [3]
   Proof:   a DIV b
          = 1 * (a DIV b)                            by MULT_LEFT_1
          = (n DIV n) * (a DIV b)                    by DIVMOD_ID, 0 < n
          = (n * a) DIV (n * b)                      by assumption
          = (n * a) DIV (k * (2 * b))                by arithmetic, n = 2 * k
          = (n DIV k) * (a DIV (2 * b))              by assumption
          = 2 * (a DIV (2 * b))                      by n DIV k = 2

   Claim: !a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))    [4]
   Proof: Let c = b ** h.
          Then b = c * c               by EXP_EXP_MULT
            so 0 < c                   by MULT_EQ_0, 0 < b
              a * (c DIV b)
            = (c DIV b) * a            by MULT_COMM
            = (a * c) DIV b            by [2]
            = (a * c) DIV (c * c)      by b = c * c
            = (a DIV c) * (c DIV c)    by assumption
            = a DIV c                  by DIVMOD_ID, c DIV c = 1, 0 < c

   Note  (FACT k) ** 2
       = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2    by EXP_BASE_MULT
       = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n           by EXP_EXP_MULT, n = 2 * k
       = (SQRT (pi * n)) ** 2 * (k DIV e) ** n               by MULT_ASSOC, 2 * k = n
       = ((pi * n) ** h) ** 2 * (k DIV e) ** n               by assumption
       = (pi * n) * (k DIV e) ** n                           by EXP_EXP_MULT, h * 2 = 1

     binomial n (HALF n)
   = binomial n k                             by k = HALF n
   = FACT n DIV (FACT k * FACT (n - k))       by binomial_formula3, k <= n
   = FACT n DIV (FACT k * FACT k)             by arithmetic, n - k = 2 * k - k = k
   = FACT n DIV ((FACT k) ** 2)               by EXP_2
   = FACT n DIV ((pi * n) * (k DIV e) ** n)   by above
   = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)        by assumption
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))    by (a * b) DIV (x * y) = (a DIV x) * (b DIV y)
   = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n           by (a ** n) DIV (b ** n) = (a DIV b) ** n)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n   by MULT_ASSOC, a DIV b = 2 * a DIV (2 * b)
   = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n                   by assumption, apply DIV_DIV_DIV_MULT
   = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n                                    by 2 * x ** h DIV x = 2 DIV (x ** h)
   = 2 DIV (2 * pi * n) ** h * 2 ** n                                            by n DIV k = 2
   = 2 * 2 ** n DIV (2 * pi * n) ** h                                            by (a DIV b) * c = a * c DIV b
   = 2 ** (SUC n) DIV (2 * pi * n) ** h                                          by EXP
   = 2 ** (n + 1)) DIV (SQRT (2 * pi * n))                                       by ADD1, assumption
*)
val binomial_middle_by_stirling = store_thm(
  "binomial_middle_by_stirling",
  ``Stirling ==> !n. 0 < n /\ EVEN n ==> (binomial n (HALF n) = (2 ** (n + 1)) DIV (SQRT (2 * pi * n)))``,
  rpt strip_tac >>
  `HALF n <= n /\ (n = 2 * HALF n)` by rw[DIV_LESS_EQ, EVEN_HALF] >>
  qabbrev_tac `k = HALF n` >>
  `0 < k` by decide_tac >>
  `n DIV k = 2` by metis_tac[MULT_TO_DIV, MULT_COMM] >>
  `0 < pi * n` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `0 < 2 * pi * n` by decide_tac >>
  `(FACT k) ** 2 = (SQRT (2 * pi * k)) ** 2 * ((k DIV e) ** k) ** 2` by rw[EXP_BASE_MULT] >>
  `_ = (SQRT (2 * pi * k)) ** 2 * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  `_ = (pi * n) * (k DIV e) ** n` by rw[GSYM EXP_EXP_MULT] >>
  (`!a b j. (a ** j) DIV (b ** j) = (a DIV b) ** j` by (Induct_on `j` >> rw[EXP])) >>
  `!a b c. (a DIV b) * c = (a * c) DIV b` by metis_tac[DIV_1, MULT_RIGHT_1] >>
  `!a b. a DIV b = 2 * (a DIV (2 * b))` by metis_tac[DIVMOD_ID, MULT_LEFT_1] >>
  `!a b. 0 < b ==> (a * (b ** h DIV b) = a DIV (b ** h))` by
  (rpt strip_tac >>
  qabbrev_tac `c = b ** h` >>
  `b = c * c` by rw[GSYM EXP_EXP_MULT, Abbr`c`] >>
  `0 < c` by metis_tac[MULT_EQ_0, NOT_ZERO] >>
  `a * (c DIV b) = (a * c) DIV (c * c)` by metis_tac[MULT_COMM] >>
  `_ = (a DIV c) * (c DIV c)` by metis_tac[] >>
  metis_tac[DIVMOD_ID, MULT_RIGHT_1]) >>
  `binomial n k = (FACT n) DIV (FACT k * FACT (n - k))` by metis_tac[binomial_formula3] >>
  `_ = (FACT n) DIV (FACT k) ** 2` by metis_tac[EXP_2, DECIDE``2 * k - k = k``] >>
  `_ = ((2 * pi * n) ** h * (n DIV e) ** n) DIV ((pi * n) * (k DIV e) ** n)` by prove_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) ** n DIV ((k DIV e) ** n))` by metis_tac[] >>
  `_ = ((2 * pi * n) ** h DIV (pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * ((n DIV e) DIV (k DIV e)) ** n` by metis_tac[MULT_ASSOC] >>
  `_ = 2 * ((2 * pi * n) ** h DIV (2 * pi * n)) * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * (n DIV k) ** n` by metis_tac[] >>
  `_ = 2 DIV (2 * pi * n) ** h * 2 ** n` by metis_tac[] >>
  `_ = (2 * 2 ** n DIV (2 * pi * n) ** h)` by metis_tac[] >>
  metis_tac[EXP, ADD1]);

(* ------------------------------------------------------------------------- *)
(* Useful theorems for Binomial                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k MOD n = 0) <=>
            !h. 0 <= h /\ h < PRE n ==> (binomial n (SUC h) MOD n = 0) *)
(* Proof: by h = PRE k, or k = SUC h.
   If part: put k = SUC h,
      then 0 < SUC h ==>  0 <= h,
       and SUC h < n ==> PRE (SUC h) = h < PRE n  by prim_recTheory.PRE
   Only-if part: put h = PRE k,
      then 0 <= PRE k ==> 0 < k
       and PRE k < PRE n ==> k < n                by INV_PRE_LESS
*)
val binomial_range_shift = store_thm(
  "binomial_range_shift",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                   (!h. h < PRE n ==> ((binomial n (SUC h)) MOD n = 0)))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: binomial n k MOD n = 0 <=> (binomial n k * x ** (n-k) * y ** k) MOD n = 0 *)
(* Proof:
       (binomial n k * x ** (n-k) * y ** k) MOD n = 0
   <=> (binomial n k * (x ** (n-k) * y ** k)) MOD n = 0    by MULT_ASSOC
   <=> (((binomial n k) MOD n) * ((x ** (n - k) * y ** k) MOD n)) MOD n = 0  by MOD_TIMES2
   If part, apply 0 * z = 0  by MULT.
   Only-if part, pick x = 1, y = 1, apply EXP_1.
*)
val binomial_mod_zero = store_thm(
  "binomial_mod_zero",
  ``!n. 0 < n ==> !k. (binomial n k MOD n = 0) <=> (!x y. (binomial n k * x ** (n-k) * y ** k) MOD n = 0)``,
  rw_tac std_ss[EQ_IMP_THM] >-
  metis_tac[MOD_TIMES2, ZERO_MOD, MULT] >>
  metis_tac[EXP_1, MULT_RIGHT_1]);


(* Theorem: (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
            (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))) *)
(* Proof: by h = PRE k, or k = SUC h. *)
val binomial_range_shift_alt = store_thm(
  "binomial_range_shift_alt",
  ``!n . 0 < n ==> ((!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0))) <=>
                   (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    `0 < SUC h /\ SUC h < n` by decide_tac >>
    rw_tac std_ss[],
    `k <> 0` by decide_tac >>
    `?h. k = SUC h` by metis_tac[num_CASES] >>
    `h < PRE n` by decide_tac >>
    rw_tac std_ss[]
  ]);

(* Theorem: !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0 <=>
            !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0 *)
(* Proof:
       !k. 0 < k /\ k < n ==> (binomial n k) MOD n = 0
   <=> !k. 0 < k /\ k < n ==> !x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)   by binomial_mod_zero
   <=> !h. h < PRE n ==> !x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)  by binomial_range_shift_alt
   <=> !x y. EVERY (\z. z = 0) (GENLIST (\k. (binomial n (SUC k) * x ** (n - (SUC k)) * y ** (SUC k)) MOD n) (PRE n)) by EVERY_GENLIST
   <=> !x y. EVERY (\x. x = 0) (GENLIST ((\k. binomial n k * x ** (n - k) * y ** k) o SUC) (PRE n)  by FUN_EQ_THM
   <=> !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0   by SUM_EQ_0
*)
val binomial_mod_zero_alt = store_thm(
  "binomial_mod_zero_alt",
  ``!n. 0 < n ==> ((!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
                  !x y. SUM (GENLIST ((\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC) (PRE n)) = 0)``,
  rpt strip_tac >>
  `!x y. (\k. (binomial n (SUC k) * x ** (n - SUC k) * y ** (SUC k)) MOD n) = (\k. (binomial n k * x ** (n - k) * y ** k) MOD n) o SUC` by rw_tac std_ss[FUN_EQ_THM] >>
  `(!k. 0 < k /\ k < n ==> ((binomial n k) MOD n = 0)) <=>
    (!k. 0 < k /\ k < n ==> (!x y. ((binomial n k * x ** (n - k) * y ** k) MOD n = 0)))` by rw_tac std_ss[binomial_mod_zero] >>
  `_ = (!h. h < PRE n ==> (!x y. ((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0)))` by rw_tac std_ss[binomial_range_shift_alt] >>
  `_ = !x y h. h < PRE n ==> (((binomial n (SUC h) * x ** (n - (SUC h)) * y ** (SUC h)) MOD n = 0))` by metis_tac[] >>
  rw_tac std_ss[EVERY_GENLIST, SUM_EQ_0]);


(* ------------------------------------------------------------------------- *)
(* Binomial Theorem with prime exponent                                      *)
(* ------------------------------------------------------------------------- *)


(* Theorem: [Binomial Expansion for prime exponent]  (x + y)^p = x^p + y^p (mod p) *)
(* Proof:
     (x+y)^p  (mod p)
   = SUM (k=0..p) C(p,k)x^(p-k)y^k  (mod p)                                     by binomial theorem
   = (C(p,0)x^py^0 + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + C(p,p)x^0y^p) (mod p)  by breaking sum
   = (x^p + SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k + y^k) (mod p)                    by binomial_n_0, binomial_n_n
   = ((x^p mod p) + (SUM (k=1..(p-1)) C(p,k)x^(p-k)y^k) (mod p) + (y^p mod p)) mod p   by MOD_PLUS
   = ((x^p mod p) + (SUM (k=1..(p-1)) (C(p,k)x^(p-k)y^k) (mod p)) + (y^p mod p)) mod p
   = (x^p mod p  + 0 + y^p mod p) mod p                                         by prime_iff_divides_binomials
   = (x^p + y^p) (mod p)                                                        by MOD_PLUS
*)
val binomial_thm_prime = store_thm(
  "binomial_thm_prime",
  ``!p. prime p ==> (!x y. (x + y) ** p MOD p = (x ** p + y ** p) MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  `!k. 0 < k /\ k < p ==> ((binomial p k) MOD p  = 0)` by metis_tac[prime_iff_divides_binomials, DIVIDES_MOD_0] >>
  `SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) MOD p = 0` by metis_tac[SUM_GENLIST_MOD, binomial_mod_zero_alt, ZERO_MOD] >>
  `(x + y) ** p MOD p = (x ** p + SUM (GENLIST ((\k. binomial p k * x ** (p - k) * y ** k) o SUC) (PRE p)) + y ** p) MOD p` by rw_tac std_ss[binomial_thm, SUM_DECOMPOSE_FIRST_LAST, binomial_n_0, binomial_n_n, EXP] >>
  metis_tac[MOD_PLUS3, ADD_0, MOD_PLUS]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
