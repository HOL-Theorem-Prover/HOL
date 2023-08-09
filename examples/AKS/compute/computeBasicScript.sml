(* ------------------------------------------------------------------------- *)
(* Basic Computations                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computeBasic";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperFunctionTheory"; -- in ringTheory *) *)
(* (* val _ = load "helperListTheory"; -- in polyRingTheory *) *)
(* val _ = load "logPowerTheory"; *)
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory;
open pred_setTheory listTheory arithmeticTheory;

open logPowerTheory; (* for LOG2, SQRT, and Perfect Power, Power Free *)
open logrootTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* val _ = load "GaussTheory"; *)
open EulerTheory;
open GaussTheory;

(* val _ = load "whileTheory"; *)
open whileTheory;


(* ------------------------------------------------------------------------- *)
(* Basic Computations Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
   sqrt_compute  = root_compute 2
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   LOG2 Computation:
   log_compute_def     |- !n. log_compute n =
                                   if n = 0 then LOG2 0
                              else if n = 1 then 0
                              else 1 + log_compute (HALF n)
   log_compute_eqn     |- !n. log_compute n = LOG2 n
   ulog_step_def       |- !n m k. ulog_step n m k =
                                       if m = 0 then 0
                                  else if n <= m then k
                                  else ulog_step n (TWICE m) (SUC k)
   ulog_step_eq_count_up   |- !n m k. ulog_step n m k = count_up n m k
   ulog_compute_def    |- !n. ulog_compute n = ulog_step n 1 0
   ulog_compute_eqn    |- !n. ulog_compute n = ulog n


   Power Computation:
   exp_binary_def      |- !n m. exp_binary m n =
                                 if n = 0 then 1
                                 else (let r = exp_binary (m * m) (HALF n) in
                                       if EVEN n then r else m * r)
   exp_binary_0        |- !m. exp_binary m 0 = 1
   exp_binary_1        |- !m. exp_binary m 1 = m
   exp_binary_even     |- !m n. EVEN n ==> (exp_binary m n = exp_binary (m * m) (HALF n))
   exp_binary_odd      |- !m n. ODD n ==> (exp_binary m n = m * exp_binary (m * m) (HALF n))
   exp_binary_suc      |- !m n. exp_binary m (SUC n) = m * exp_binary m n
   exp_binary_eqn      |- !m n. exp_binary m n = m ** n
   exp_binary_of_0     |- !n. exp_binary 0 n = if n = 0 then 1 else 0

   Fast Exponentiation:
   exp_step_def        |- !r n m. exp_step m n r = if n = 0 then r
                                  else exp_step (SQ m) (HALF n) (if EVEN n then r else r * m)
   exp_compute_def     |- !m n. exp_compute m n = exp_step m n 1
   exp_step_0          |- !m r. exp_step m 0 r = r
   exp_step_1          |- !m r. exp_step m 1 r = r * m
   exp_step_2          |- !m r. exp_step m 2 r = r * m * m
   exp_step_even       |- !n. EVEN n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) r
   exp_step_odd        |- !n. ODD n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) (r * m)
   exp_step_eqn        |- !m n r. exp_step m n r = r * m ** n
   exp_compute_0       |- !m. exp_compute m 0 = 1
   exp_compute_1       |- !m. exp_compute m 1 = m
   exp_compute_2       |- !m. exp_compute m 2 = SQ m
   exp_compute_even    |- !n. EVEN n ==> !m. exp_compute m n = exp_compute (SQ m) (HALF n)
   exp_compute_eqn     |- !m n. exp_compute m n = m ** n

   Modular Exponentiation:
   exp_mod_binary_def   |- !n m a. exp_mod_binary a n m =
                                        if m = 0 then a ** n MOD 0
                                   else if m = 1 then 0
                                   else if n = 0 then 1
                                   else (let b = exp_mod_binary ((a * a) MOD m) (HALF n) m
                                          in if EVEN n then b else (a * b) MOD m)
   exp_mod_binary_0     |- !a m. 0 < m ==> (exp_mod_binary a 0 m = if m = 1 then 0 else 1)
   exp_mod_binary_1     |- !a m. exp_mod_binary a 1 m = a MOD m
   exp_mod_binary_even  |- !m n. 0 < m /\ EVEN n ==>
                           !a. exp_mod_binary a n m = exp_mod_binary ((a * a) MOD m) (HALF n) m
   exp_mod_binary_odd   |- !m n. 0 < m /\ ODD n ==>
                           !a. exp_mod_binary a n m = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m
   exp_mod_binary_suc   |- !m n. 0 < m ==> !a. exp_mod_binary a (SUC n) m = (a * exp_mod_binary a n m) MOD m
   exp_mod_binary_eqn   |- !m n a. exp_mod_binary a n m = a ** n MOD m
   exp_mod_binary_0_n   |- !m n. exp_mod_binary 0 n m = (if n = 0 then 1 else 0) MOD m

   Fast Modular Exponentiation:
   exp_mod_step_def     |- !r n m k. exp_mod_step m n k r = if k = 0 then (r * m ** n) MOD k
                                     else if n = 0 then r MOD k
                                     else exp_mod_step (SQ m MOD k) (HALF n) k
                                                       (if EVEN n then r else (r * m) MOD k)
   exp_mod_compute_def  |- !m n k. exp_mod_compute m n k = exp_mod_step m n k 1
   exp_mod_step_0       |- !m r k. exp_mod_step m 0 k r = r MOD k
   exp_mod_step_1       |- !m r k. exp_mod_step m 1 k r = (r * m) MOD k
   exp_mod_step_2       |- !m r k. exp_mod_step m 2 k r = (r * m * m) MOD k
   exp_mod_step_even    |- !k. 0 < k ==> !n. EVEN n ==>
                           !m r. exp_mod_step m n k r = exp_mod_step (SQ m MOD k) (HALF n) k r
   exp_mod_step_odd     |- !k. 0 < k ==> !n. ODD n ==>
                           !m r. exp_mod_step m n k r = exp_mod_step (SQ m MOD k) (HALF n) k ((r * m) MOD k)
   exp_mod_step_eqn     |- !m n k r. exp_mod_step m n k r = (r * m ** n) MOD k
   exp_mod_compute_0    |- !m k. exp_mod_compute m 0 k = 1 MOD k
   exp_mod_compute_1    |- !m k. exp_mod_compute m 1 k = m MOD k
   exp_mod_compute_2    |- !m k. exp_mod_compute m 2 k = SQ m MOD k
   exp_mod_compute_even |- !k. 0 < k ==> !n. EVEN n ==>
                           !m. exp_mod_compute m n k = exp_mod_compute (SQ m MOD k) (HALF n) k
   exp_mod_compute_odd  |- !k. 0 < k ==> !n. ODD n ==>
                           !m. exp_mod_compute m n k = exp_mod_step (SQ m MOD k) (HALF n) k (m MOD k)
   exp_mod_compute_eqn  |- !m n k. exp_mod_compute m n k = m ** n MOD k

   ROOT computation:
   root_compute_def     |- !r n. root_compute r n =
                                 if 0 < r then
                                    if n = 0 then 0 else
                                    (let x = 2 * root_compute r (n DIV exp_compute 2 r)
                                      in if n < exp_compute (SUC x) r then x else SUC x)
                                 else ROOT 0 n
   root_compute_alt     |- !r n. root_compute r n =
                                 if 0 < r then
                                    if n = 0 then 0 else
                                    (let x = 2 * root_compute r (n DIV 2 ** r)
                                      in if n < SUC x ** r then x else SUC x)
                                 else ROOT 0 n
   root_compute_0       |- !r. 0 < r ==> (root_compute r 0 = 0)
   root_compute_1       |- !n. root_compute 1 n = n
   root_compute_eqn     |- !r n. root_compute r n = ROOT r n
   sqrt_compute_eqn     |- !n. sqrt_compute n = SQRT n

   Power Free Test:
   power_index_compute_def   |- !n k. power_index_compute n k =
                                           if k <= 1 then 1
                                      else if exp_compute (root_compute k n) k = n then k
                                      else power_index_compute n (k - 1)
   power_index_compute_alt   |- !n k. power_index_compute n k =
                                           if k <= 1 then 1
                                      else if ROOT k n ** k = n then k
                                      else power_index_compute n (k - 1)
   power_index_compute_eqn   |- !n k. power_index_compute n k = power_index n k
   power_free_check_def      |- !n. power_free_check n <=>
                                    1 < n /\ (power_index_compute n (ulog_compute n) = 1)
   power_free_check_0        |- power_free_check 0 <=> F
   power_free_check_1        |- power_free_check 1 <=> F
   power_free_check_alt      |- !n. power_free_check n <=> 1 < n /\ (power_index n (ulog n) = 1)
   power_free_check_eqn      |- !n. power_free_check n <=> power_free n
!  power_free_eval           |- !n. power_free n <=> power_free_check n
   power_free_check_by_ulog  |- !n. power_free_check n <=> 1 < n /\ (power_index n (ulog n) = 1)
   power_free_check_by_LOG2  |- !n. power_free_check n <=> 1 < n /\ (power_index n (LOG2 n) = 1)

   GCD computation:
   ODD_IMP_GCD_CANCEL_EVEN  |- !m n. ODD n ==> (gcd n (2 * m) = gcd n m)
   BINARY_GCD               |- !m n. (EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (HALF m) (HALF n))) /\
                                     (EVEN m /\ ODD n ==> (gcd m n = gcd (HALF m) n))
   gcd_compute_def          |- !n m. gcd_compute n m =
                                          if n = 0 then m
                                     else if m = 0 then n
                                     else if n = m then n
                                     else if EVEN n then
                                          if EVEN m then 2 * gcd_compute (HALF n) (HALF m)
                                                    else gcd_compute (HALF n) m
                                     else if EVEN m then gcd_compute n (HALF m)
                                                    else if n < m then gcd_compute n (m - n)
                                                                  else gcd_compute (n - m) m
   gcd_compute_0            |- !n. (gcd_compute 0 n = n) /\ (gcd_compute n 0 = n)
   gcd_compute_id           |- !n. gcd_compute n n = n
   gcd_compute_even_even    |- !m n. EVEN n /\ EVEN m ==> (gcd_compute n m = 2 * gcd_compute (HALF n) (HALF m))
   gcd_compute_even_odd     |- !m n. EVEN n /\ ODD m ==> (gcd_compute n m = gcd_compute (HALF n) m)
   gcd_compute_odd_even     |- !m n. ODD n /\ EVEN m ==> (gcd_compute n m = gcd_compute n (HALF m))
   gcd_compute_odd_odd      |- !m n. ODD n /\ ODD m ==>
                               (gcd_compute n m = if n < m then gcd_compute n (m - n) else gcd_compute (n - m) m)
   gcd_compute_eqn          |- !m n. gcd_compute n m = gcd n m
   gcd_compute_1            |- !n. (gcd_compute 1 n = 1) /\ (gcd_compute n 1 = 1)
   gcd_compute_sym          |- !m n. gcd_compute n m = gcd_compute m n

   Phi Computation:
   count_coprime_def    |- !n j. count_coprime n j =
                                      if j = 0 then 0
                                 else if j = 1 then 1
                                 else count_coprime n (j - 1) + if gcd_compute j n = 1 then 1 else 0
   phi_compute_def      |- !n. phi_compute n = count_coprime n n
   phi_compute_0        |- phi_compute 0 = 0
   phi_compute_1        |- phi_compute 1 = 1
   count_coprime_0      |- !n. count_coprime n 0 = 0
   count_coprime_1      |- !n. count_coprime n 1 = 1
   count_coprime_alt    |- !n j. count_coprime n j =
                                      if j = 0 then 0
                                 else if j = 1 then 1
                                 else count_coprime n (j - 1) + if coprime j n then 1 else 0
   count_coprime_suc    |- !n k. count_coprime n (SUC k) = count_coprime n k + if coprime (SUC k) n then 1 else 0
   count_coprime_eqn    |- !n k. k <= n ==> (count_coprime n k = CARD (coprimes n INTER natural k))
   phi_compute_eqn      |- !n. phi_compute n = phi n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Computations                                                              *)
(* ------------------------------------------------------------------------- *)

(* There are several computations to investigate:

** LOG2 computation
** Phi computation
** Fast exponentiation
** Fast modulo exponentiation
** Order computation by fast exponentiation

** Root computation
** Perfect-power check by root computation
** Special square-root computation?

** Binary GCD computation
** Euler phi computation by binary GCD computation
** Coprime check by binary GCD computation?

** Polynomial Addition under modulus (modulus is irrelevant)
** Polynomial Multiplication under modulus (by rewriting)
** Polynomial Introspective efficient check under modulus X ** k - |1|

*)

(* ------------------------------------------------------------------------- *)
(* LOG2 Computation                                                          *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: n with 0 < n
Output: log2 n

c <- 0             // initial count
while (1 < n) {
   c <- c + 1      // increment count
   n <- n DIV 2    // reduce n by half
}
return c           // the result

*)

(*
Question: Can (countdivs n) be expressed in a WHILE loop?
          Or, can we prove that (countdivs n) invokes itself at most (LOG2 n) times?
*)

(* Compute LOG2 by counting the number of divisions down to 1 *)
val log_compute_def = Define `
   log_compute n = if n = 0 then LOG2 0
                   else if n = 1 then 0
                   else 1 + log_compute (HALF n)
`;

(*
> EVAL ``log_compute 4``; --> 2
> EVAL ``log_compute 5``; --> 2
> EVAL ``log_compute 6``; --> 2
> EVAL ``log_compute 7``; --> 2
> EVAL ``log_compute 8``; --> 3
> EVAL ``log_compute 9``; --> 3
> EVAL ``log_compute 10``; --> 3
> EVAL ``log_compute 1024``; --> 10
*)

(* Theorem: log_compute n = LOG2 n *)
(* Proof:
   By complete induction on n.
   Apply log_compute_def, this is to show:
   (1) 0 = LOG2 1, true                  by LOG_1
   (1) If 1 < n ==> 1 + log_compute (HALF n) = LOG2 n
       Note 2 <= n                      by 1 < n
         so (0 + 1) * 2 <= n            by arithmetic
       Thus 0 < HALF n                  by X_LT_DIV, 0 < 2
            LOG2 n
          = 1 + LOG2 (HALF n)           by LOG_DIV, 1 < 2
          = 1 + log_compute (HALF n)    by induction hypothesis, 0 < HALF n
*)
val log_compute_eqn = store_thm(
  "log_compute_eqn",
  ``!n. log_compute n = LOG2 n``,
  completeInduct_on `n` >>
  rw_tac std_ss[Once log_compute_def] >-
  rw[LOG_1] >>
  rw[LOG_DIV, X_LT_DIV]);

(* For the cost:
f(n) --> cost_f(n)
add1(n) --> cost_add1(n) = log n
half(n) --> cost_half(n) = 1
log(n) --> cost_log(n) = ???   by log_compute_def
                       = cost_add1(n) + ... + cost_log(half n)
*)

(* Compute ulog by counting the number of doubles than equal or exceeds n *)
(* This is just count_up renamed to ulog_step *)
Definition ulog_step_def:
  ulog_step n m k =
       if m = 0 then 0 (* just to provide m <> 0 for the next one *)
  else if n <= m then k else ulog_step n (2 * m) (SUC k)
Termination WF_REL_TAC `measure (λ(n, m, k). n - m)`
End

(* Theorem: ulog_step n m k = count_up n m k *)
(* Proof: by ulog_step_def, count_up_def *)
val ulog_step_eq_count_up = store_thm(
  "ulog_step_eq_count_up",
  ``!n m k. ulog_step n m k = count_up n m k``,
  ntac 2 strip_tac >>
  completeInduct_on `n - m` >>
  simp[Once ulog_step_def] >>
  rpt strip_tac >>
  metis_tac[count_up_def]);

(* Define upper LOG2 n by ulog_step *)
val ulog_compute_def = Define`
    ulog_compute n = ulog_step n 1 0
`;

(*
> EVAL ``ulog_compute 4``; --> 2
> EVAL ``ulog_compute 5``; --> 3
> EVAL ``ulog_compute 6``; --> 3
> EVAL ``ulog_compute 7``; --> 3
> EVAL ``ulog_compute 8``; --> 3
> EVAL ``ulog_compute 9``; --> 4
> EVAL ``ulog_compute 10``; --> 4
> EVAL ``ulog_compute 1024``; --> 10
*)

(* Theorem: ulog_compute n = ulog n *)
(* Proof: by ulog_compute_def, ulog_def, ulog_step_eq_count_up *)
val ulog_compute_eqn = store_thm(
  "ulog_compute_eqn",
  ``!n. ulog_compute n = ulog n``,
  rw[ulog_compute_def, ulog_def, ulog_step_eq_count_up]);

(* ------------------------------------------------------------------------- *)
(* Power Computation (Fast Exponential Computation)                          *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: m n
Output: m ** n

if (m == 1) return 1    // quick check for convenience only
if (n == 1) return m    // quick check for convenience only

r <- 1                  // initial result
while (n <> 0) {
    if (EVEN n) {       // even exponent
       n <- HALF n      // reduce exponent by half
       m <- m * m       // update base by its square
    }
    else {              // odd exponent
       n <- n - 1       // make exponent even
       r <- r * m       // update result by multiplying with base
    }
}
return r // the result

Since the exponent n is decreasing (either by half or by one) in each iteration, the while-loop terminates.

Recursive version:
if (n = 0) then 1
else (* precompute *) r <- (m * m) ** (HALF n)
     (* now the result *) if EVEN n then r else m * r
*)

(* Define exponentiation by repeated squaring. *)
val exp_binary_def = Define`
   exp_binary (m:num) n =
      if (n = 0) then 1  (* m ** 0 = 1 *)
      (* either n or (n - 1) is EVEN, precompute the repeated square *)
      else let r = exp_binary (m * m) (HALF n) in
      if EVEN n then r else m * r (* if EVEN, return reuslt, otherwise multiply by base for ODD *)
`;

(*
> EVAL ``exp_binary 3 2``; --> 9
> EVAL ``exp_binary 3 3``; --> 27
> EVAL ``exp_binary 3 4``; --> 81
> EVAL ``exp_binary 3 5``; --> 243
> EVAL ``exp_binary 2 10``; --> 1024
> EVAL ``exp_binary 3 10``; --> 59049
*)

(* Theorem: exp_binary m 0 = 1 *)
(* Proof: by exp_binary_def *)
val exp_binary_0 = store_thm(
  "exp_binary_0",
  ``!m. exp_binary m 0 = 1``,
  rw[Once exp_binary_def]);

(* Theorem: exp_binary m 1 = m *)
(* Proof: by exp_binary_def *)
val exp_binary_1 = store_thm(
  "exp_binary_1",
  ``!m. exp_binary m 1 = m``,
  rw[Once exp_binary_def] >>
  rw[Once exp_binary_def]);

(* Theorem: EVEN n ==> (exp_binary m n = exp_binary (m * m) (HALF n)) *)
(* Proof:
   If n = 0, true by      exp_binary_0, HALF 0 = 0.
   If n <> 0, true by     exp_binary_def
*)
val exp_binary_even = store_thm(
  "exp_binary_even",
  ``!m n. EVEN n ==> (exp_binary m n = exp_binary (m * m) (HALF n))``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[exp_binary_0] >>
  rw[Once exp_binary_def]);

(* Theorem: ODD n ==> (exp_binary m n = m * exp_binary (m * m) (HALF n)) *)
(* Proof:
   Note ODD 0 = F           by ODD
    and ODD n = ~(EVEN n)   by ODD_EVEN
   Thus true                by exp_binary_def
*)
val exp_binary_odd = store_thm(
  "exp_binary_odd",
  ``!m n. ODD n ==> (exp_binary m n = m * exp_binary (m * m) (HALF n))``,
  rw_tac std_ss[Once exp_binary_def] >>
  metis_tac[ODD_EVEN]);

(* Theorem: exp_binary m (SUC n) = m * exp_binary m n *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Then ODD (SUC n)                           by EVEN_ODD_SUC
        exp_binary m (SUC n)
      = m * exp_binary (m * m) (HALF (SUC n))    by exp_binary_odd
      = m * exp_binary (m * m) (HALF n)          by EVEN_SUC_HALF
      = m * exp_binary m n                       by exp_binary_even

   If ~(EVEN n), then ODD n                      by EVEN_ODD
      Then EVEN (SUC n)                          by EVEN_ODD_SUC
      Note n <> 0                                by ODD, ODD 0 = F.
      Thus HALF n < n                            by DIV_LESS, 0 < n, 1 < 2.
        m * exp_binary m n
      = m * m * exp_binary (m * m) (HALF n)      by exp_binary_odd
      = exp_binary (m * m) (SUC (HALF n))        by induction hypothesis, HALF n < n.
      = exp_binary (m * m) (HALF (SUC n))        by ODD_SUC_HALF
      = exp_binary m (SUC n)                     by exp_binary_even
*)
val exp_binary_suc = store_thm(
  "exp_binary_suc",
  ``!m n. exp_binary m (SUC n) = m * exp_binary m n``,
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `ODD (SUC n)` by rw[GSYM EVEN_ODD_SUC] >>
    `exp_binary m (SUC n) = m * exp_binary (m * m) (HALF (SUC n))` by rw[exp_binary_odd] >>
    `_ = m * exp_binary (m * m) (HALF n)` by rw[EVEN_SUC_HALF] >>
    `_ = m * exp_binary m n` by rw[exp_binary_even] >>
    rw[],
    `ODD n` by metis_tac[EVEN_ODD] >>
    `EVEN (SUC n)` by rw[GSYM EVEN_ODD_SUC] >>
    `n <> 0` by metis_tac[ODD] >>
    `HALF n < n` by rw[] >>
    `m * exp_binary m n = m * m * exp_binary (m * m) (HALF n)` by rw[exp_binary_odd] >>
    `_ = exp_binary (m * m) (SUC (HALF n))` by rw[] >>
    `_ = exp_binary (m * m) (HALF (SUC n))` by rw[ODD_SUC_HALF] >>
    `_ = exp_binary m (SUC n)` by rw[exp_binary_even] >>
    rw[]
  ]);

(* Theorem: exp_binary m n = m ** n *)
(* Proof:
   By induction on n.
   Base: exp_binary m 0 = m ** 0
       exp_binary m 0
     = 1                      by exp_binary_0
     = m ** 0                 by EXP
   Step: exp_binary m n = m ** n ==> exp_binary m (SUC n) = m ** SUC n
       exp_binary m (SUC n)
     = m * exp_binary m n     by exp_binary_suc
     = m * m ** n             by induction hypothesis
     = m ** SUC n             by EXP
*)
val exp_binary_eqn = store_thm(
  "exp_binary_eqn",
  ``!m n. exp_binary m n = m ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[exp_binary_0] >>
  rw[exp_binary_suc, EXP]);

(* Theorem: exp_binary 0 n = if n = 0 then 1 else 0 *)
(* Proof:
     exp_binary 0 n
   = 0 ** n                  by exp_binary_eqn
   = if n = 0 then 1 else 0  by ZERO_EXP
*)
val exp_binary_of_0 = store_thm(
  "exp_binary_of_0",
  ``!n. exp_binary 0 n = if n = 0 then 1 else 0``,
  rw[exp_binary_eqn]);

(* ------------------------------------------------------------------------- *)
(* Fast Exponentiation (Repeated Squares Method)                             *)
(* ------------------------------------------------------------------------- *)

(* Fast Exponentiation -- iterative form *)
(* Pseudo-Code:
   m ** n = r <- 1
            loop:
            if (n == 0) return r
            if (ODD n) r <- r * m
            n <- HALF n
            m <- SQ m
            goto loop
*)

(* Define fast exponentiation *)
val exp_step_def = Define`
    exp_step m n r = (* r = m ** n *)
       if n = 0 then r else
       exp_step (SQ m) (HALF n) (if EVEN n then r else r * m)
`;
val exp_compute_def = Define`
    exp_compute m n = exp_step m n 1
`;

(*
EVAL ``exp_compute 2 10``; --> 1024
EVAL ``exp_compute 3 10``; --> 59049
EVAL ``exp_compute 3 8 = 3 ** 8``; --> T
*)

(* Theorem: exp_step m 0 r = r *)
(* Proof: by exp_step_def *)
val exp_step_0 = store_thm(
  "exp_step_0",
  ``!m r. exp_step m 0 r = r``,
  rw[Once exp_step_def]);

(* Theorem: exp_step m 1 r = r * m *)
(* Proof: by exp_step_def *)
val exp_step_1 = store_thm(
  "exp_step_1",
  ``!m r. exp_step m 1 r = r * m``,
  rw[Once exp_step_def, Once exp_step_def]);

(* Theorem: exp_step m 2 r = r * m * m *)
(* Proof:
     exp_step m 2 r
   = exp_step (SQ m) (HALF 2) r     by exp_step_def, EVEN 2
   = exp_step (SQ m) 1 r            by arithmetic
   = r * SQ m                       by exp_step_1
   = r * (m * m)                    by EXP_2
   = r * m * m                      by MULT_ASSOC
*)
val exp_step_2 = store_thm(
  "exp_step_2",
  ``!m r. exp_step m 2 r = r * m * m``,
  rw[Once exp_step_def, Once exp_step_def, Once exp_step_def]);

(* Theorem: EVEN n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) r *)
(* Proof:
   If n = 0, HALF 0 = 0      by HALF_EQ_0
      Thus LHS = r = RHS     by exp_step_def
   If n <> 0, true           by exp_step_def
*)
val exp_step_even = store_thm(
  "exp_step_even",
  ``!n. EVEN n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) r``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[exp_step_def, HALF_EQ_0] >>
  rw[Once exp_step_def]);

(* Theorem: ODD n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) (r * m) *)
(* Proof:
   Note ODD n ==> ~EVEN n     by ODD_EVEN
               and n <> 0     by EVEN
   The result follows         by exp_step_def
*)
val exp_step_odd = store_thm(
  "exp_step_odd",
  ``!n. ODD n ==> !m r. exp_step m n r = exp_step (SQ m) (HALF n) (r * m)``,
  rpt strip_tac >>
  `~EVEN n /\ n <> 0` by metis_tac[ODD_EVEN, EVEN] >>
  rw[Once exp_step_def]);

(* Theorem: exp_step m n r = r * m ** n *)
(* Proof:
   By complete induction on n.
   If n = 0,
        exp_step m 0 r
      = r                                    by exp_step_0
      = r * 1                                by MULT_RIGHT_1
      = r * m ** 0                           by EXP_0
   If n <> 0,
      then HALF n < n                        by HALF_LT, 0 < n
   If EVEN n,
        exp_step m n r
      = exp_step (SQ m) (HALF n) r           by exp_step_even
      = r * (SQ m) ** (HALF n)               by induction hypothesis, HALF n < n
      = r * m ** n                           by EXP_EVEN
   If ~EVEN n,
      then ODD n                             by EVEN_ODD
        exp_step m n r
      = exp_step (SQ m) (HALF n) (r * m)     by exp_step_odd
      = (r * m) * (SQ m) ** (HALF n)         by induction hypothesis, HALF n < n
      = r * (m * (SQ m) ** (HALF n))         by MULT_ASSOC
      = r * m ** n                           by EXP_ODD
*)
val exp_step_eqn = store_thm(
  "exp_step_eqn",
  ``!m n r. exp_step m n r = r * m ** n``,
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[exp_step_0] >>
  `HALF n < n` by rw[] >>
  Cases_on `EVEN n` >-
  rw[exp_step_even, GSYM EXP_EVEN] >>
  metis_tac[ODD_EVEN, exp_step_odd, MULT_ASSOC, EXP_ODD]);

(* Theorem: exp_compute m 0 = 1 *)
(* Proof: by exp_compute_def, exp_step_0 *)
val exp_compute_0 = store_thm(
  "exp_compute_0",
  ``!m. exp_compute m 0 = 1``,
  rw[exp_compute_def, exp_step_0]);

(* Theorem: exp_compute m 1 = m *)
(* Proof: by exp_compute_def, exp_step_1 *)
val exp_compute_1 = store_thm(
  "exp_compute_1",
  ``!m. exp_compute m 1 = m``,
  rw[exp_compute_def, exp_step_1]);

(* Theorem: exp_compute m 2 = SQ m *)
(* Proof: by exp_compute_def, exp_step_2 *)
val exp_compute_2 = store_thm(
  "exp_compute_2",
  ``!m. exp_compute m 2 = SQ m``,
  rw[exp_compute_def, exp_step_2]);

(* Theorem: EVEN n ==> !m. exp_compute m n = exp_compute (SQ m) (HALF n) *)
(* Proof:
     exp_compute m n
   = exp_step m n 1               by exp_compute_def
   = exp_step (SQ m) (HALF n) 1   by exp_step_even, EVEN n
   = exp_compute (SQ m) (HALF n)  by exp_compute_def
*)
val exp_compute_even = store_thm(
  "exp_compute_even",
  ``!n. EVEN n ==> !m. exp_compute m n = exp_compute (SQ m) (HALF n)``,
  rw[exp_compute_def, exp_step_even]);

(* Theorem: exp_compute m n = m ** n *)
(* Proof:
     exp_compute m n
   = exp_step m n 1     by exp_compute_def
   = 1 * m ** n         by exp_step_eqn
   = m ** n             by MULT_LEFT_1
*)
val exp_compute_eqn = store_thm(
  "exp_compute_eqn",
  ``!m n. exp_compute m n = m ** n``,
  rw[exp_compute_def, exp_step_eqn]);

(* ------------------------------------------------------------------------- *)
(* Modular Exponentiation.                                                   *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: b n m
Output: (b ** n) MOD m

Recursive version:
if (n = 0) then return 1
if EVEN n then return (b * b MOD m) ** (HALF n)
else return b * ((b * b MOD m) ** (HALF n)) MOD m

val EXP_MOD_EQN =
   |- !b n m. 1 < m ==>
          b ** n MOD m =
          if n = 0 then 1
          else (let result = SQ b ** HALF n MOD m
                 in if EVEN n then result else (b * result) MOD m): thm
*)

(* Pseudocode:

Input: a n m
Output: (a ** n) MOD m

Iterative version:

r <- 1                  // initial result
while (n <> 0) {
    if (EVEN n) {       // even exponent
       n <- HALF n      // reduce exponent by half
       a <- a * a MOD m // update base by its square
       r <- a           // update result by new base
    }
    else {              // odd exponent
       b <- a           // save current base
       n <- n - 1       // make exponent even
       n <- HALF n      // reduce exponent by half
       a <- a * a MOD m // update base by its square
       r <- b * a MOD m // update result by multiplying with base
    }
}
return r // the result

Since the exponent n is decreasing by half in each iteration, the while-loop terminates.

*)

(* Smart definition of: a ** n (mod m) by repeated squaring *)
(*
val exp_mod_binary_def = Define`
   exp_mod_binary a n m =
          if m = 0 then (a ** n) MOD 0   (* whatever that is! *)
     else if m = 1 then 0                (* all MOD 1 = 0 *)
     else if n = 0 then 1                (* a ** 0 (mod m) = 1 *)
     (* if EVEN n then a ** n (mod m) = (a * a MOD m) ** (HALF n) *)
     else if EVEN n then exp_mod_binary ((a * a) MOD m) (HALF n) m
     (* if ODD n then a ** n (mod m) = a * ((a * a MOD m) ** (HALF n)) MOD m *)
     else (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m
`;
*)
val exp_mod_binary_def = Define`
   exp_mod_binary a n m =
          if m = 0 then (a ** n) MOD 0   (* whatever that is! *)
     else if m = 1 then 0                (* all MOD 1 = 0 *)
     else if n = 0 then 1                (* a ** 0 (mod m) = 1 *)
     (* if EVEN n then a ** n (mod m) = (a * a MOD m) ** (HALF n) *)
     (* if ODD n then a ** n (mod m) = a * ((a * a MOD m) ** (HALF n)) MOD m *)
     else (let b = exp_mod_binary ((a * a) MOD m) (HALF n) m
            in if EVEN n then b else (a * b) MOD m)
`;
(* Note the for-all order: n m a, which is good.
val it =
   |- !n m a. exp_mod_binary a n m =
     if m = 0 then a ** n MOD 0
     else if m = 1 then 0
     else if n = 0 then 1
     else (let b = exp_mod_binary ((a * a) MOD m) (HALF n) m in if EVEN n then b else (a * b) MOD m): thm
*)
(*
- type_of ``exp_mod_binary a n m``;
> val it = ``:num`` : hol_type
- type_of ``exp_mod_binary``;
> val it = ``:num -> num -> num -> num`` : hol_type
*)

(*
> EVAL ``exp_mod_binary 3 0 10``; --> 1
> EVAL ``exp_mod_binary 3 1 10``; --> 3
> EVAL ``exp_mod_binary 3 2 10``; --> 9
> EVAL ``exp_mod_binary 3 3 10``; --> 7
> EVAL ``exp_mod_binary 3 4 10``; --> 1
*)


(* Theorem: 0 < m ==> (exp_mod_binary a 0 m = if m = 1 then 0 else 1) *)
(* Proof: by exp_mod_binary_def. *)
val exp_mod_binary_0 = store_thm(
  "exp_mod_binary_0",
  ``!a m. 0 < m ==> (exp_mod_binary a 0 m = if m = 1 then 0 else 1)``,
  rw[Once exp_mod_binary_def]);

(* Theorem: exp_mod_binary a 1 m = a MOD m *)
(* Proof: by exp_mod_binary_def, exp_mod_binary_0. *)
val exp_mod_binary_1 = store_thm(
  "exp_mod_binary_1",
  ``!a m. exp_mod_binary a 1 m = a MOD m``,
  rw[Once exp_mod_binary_def] >>
  rw[exp_mod_binary_0]);

(* Theorem: 0 < m /\ EVEN n ==> !a. exp_mod_binary a n m = exp_mod_binary ((a * a) MOD m) (HALF n) m *)
(* Proof:
   If n = 0,
        exp_mod_binary a 0 m
      = 1                                             by exp_mod_binary_0
      = exp_mod_binary (((a * a) MOD m)) 0 m          by exp_mod_binary_0
      = exp_mod_binary (((a * a) MOD m)) (HALF 0) m   by ZERO_MOD, 0 < 2
   If n <> 0,
      If m = 1,
           exp_mod_binary a n 1
         = 0                                          by exp_mod_binary_def
         = exp_mod_binary ((a * a) MOD 1) (HALF n) 1  by exp_mod_binary_def
      If m <> 1, true for EVEN n                      by exp_mod_binary_def
*)
val exp_mod_binary_even = store_thm(
  "exp_mod_binary_even",
  ``!m n. 0 < m /\ EVEN n ==> !a. exp_mod_binary a n m = exp_mod_binary ((a * a) MOD m) (HALF n) m``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[exp_mod_binary_0] >>
  rw[Once exp_mod_binary_def] >>
  rw[Once exp_mod_binary_def]);

(* Theorem: 0 < m /\ ODD n ==> !a. exp_mod_binary a n m = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m *)
(* Proof:
   If m = 1,
        exp_mod_binary a n 1
      = 0                                                        by exp_mod_binary_def
      = (a * exp_mod_binary ((a * a) MOD 1) (HALF n) 1) MOD 1    by MOD_1
   If m <> 1,
       and ODD n <=> ~(EVEN n)       by ODD_EVEN
        so n <> 0                    by EVEN
      Thus true for ~(EVEN n)        by exp_mod_binary_def
*)
val exp_mod_binary_odd = store_thm(
  "exp_mod_binary_odd",
  ``!m n. 0 < m /\ ODD n ==> !a. exp_mod_binary a n m = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m``,
  rpt strip_tac >>
  Cases_on `m = 1` >-
  rw[Once exp_mod_binary_def] >>
  rpt strip_tac >>
  `~EVEN n` by rw[GSYM ODD_EVEN] >>
  `n <> 0` by metis_tac[EVEN] >>
  rw[Once exp_mod_binary_def]);

(* Theorem: 0 < m ==> !a. exp_mod_binary a (SUC n) m = (a * exp_mod_binary a n m) MOD m *)
(* Proof:
   By complete induction on n.
   If EVEN n,
      Then ODD (SUC n)                                                by EVEN_ODD_SUC
        exp_mod_binary a (SUC n) m
      = (a * exp_mod_binary ((a * a) MOD m) (HALF (SUC n)) m) MOD m   by exp_mod_binary_odd
      = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m         by EVEN_SUC_HALF
      = (a * exp_mod_binary a n m) MOD m                              by exp_mod_binary_even
   If ~(EVEN n), then ODD n.                                          by ODD_EVEN
      Note ODD n ==> n <> 0                                           by ODD
      Thus HALF n < n                                                 by DIV_LESS, 0 < n, 1 < 2
       and EVEN (SUC n)                                               by EVEN_ODD_SUC
        (a * exp_mod_binary a n m) MOD m
      = (a * (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m) MOD m     by exp_mod_binary_odd, 0 < m
      = (a * (a * exp_mod_binary ((a * a) MOD m) (HALF n) m)) MOD m           by MOD_MOD, MOD_TIMES2, 0 < m
      = (a * a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m             by MULT_ASSOC
      = (((a * a) MOD m) * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m   by MOD_MOD, MOD_TIMES2, 0 < m
      = exp_mod_binary ((a * a) MOD m) (SUC (HALF n)) m                       by induction hypothesis
      = exp_mod_binary ((a * a) MOD m) (HALF (SUC n)) m                       by ODD_SUC_HALF
      = exp_mod_binary a (SUC n) m                                            by exp_mod_binary_even, 0 < m
*)
val exp_mod_binary_suc = store_thm(
  "exp_mod_binary_suc",
  ``!m n. 0 < m ==> !a. exp_mod_binary a (SUC n) m = (a * exp_mod_binary a n m) MOD m``,
  ntac 3 strip_tac >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `EVEN n` >| [
    `ODD (SUC n)` by metis_tac[EVEN_ODD_SUC] >>
    `exp_mod_binary a (SUC n) m = (a * exp_mod_binary ((a * a) MOD m) (HALF (SUC n)) m) MOD m` by rw[exp_mod_binary_odd] >>
    `_ = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m` by rw[EVEN_SUC_HALF] >>
    `_ = (a * exp_mod_binary a n m) MOD m` by rw[exp_mod_binary_even] >>
    rw[],
    `ODD n` by rw[ODD_EVEN] >>
    `n <> 0` by metis_tac[ODD] >>
    `HALF n < n` by rw[DIV_LESS] >>
    `EVEN (SUC n)` by rw[GSYM EVEN_ODD_SUC] >>
    `(a * exp_mod_binary a n m) MOD m = (a * (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m) MOD m` by rw[exp_mod_binary_odd] >>
    `_ = ((a * a) MOD m * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m` by metis_tac[MOD_MOD, MOD_TIMES2, MULT_ASSOC] >>
    `_ = exp_mod_binary ((a * a) MOD m) (SUC (HALF n)) m` by rw[] >>
    `_ = exp_mod_binary ((a * a) MOD m) (HALF (SUC n)) m` by rw[ODD_SUC_HALF] >>
    `_ = exp_mod_binary a (SUC n) m` by rw[exp_mod_binary_even] >>
    rw[]
  ]);

(* Theorem: exp_mod_binary a n m = a ** n MOD m *)
(* Proof:
   If m = 0, true trivially                  by exp_mod_binary_def
   If m = 1,
        exp_mod_binary a n m
      = 1                                    by exp_mod_binary_def
      = (a ** n) MOD 1                       by MOD_1
   If m <> 0 and m <> 1,
   Then 1 < m.
   By induction on n.
   Base: exp_mod_binary a 0 m = a ** 0 MOD m
        exp_mod_binary a 0 m
      = 1                                    by exp_mod_binary_0
      = 1 MOD m                              by ONE_MOD, 1 < m
      = a ** 0 MOD m                         by EXP
   Step: exp_mod_binary a n m = a ** n MOD m ==> exp_mod_binary a (SUC n) m = a ** SUC n MOD m
        exp_mod_binary a (SUC n) m
      = (a * exp_mod_binary a n m) MOD m     by exp_mod_binary_suc, 0 < m
      = (a * a ** n MOD m) MOD m             by induction hypothesis
      = (a * a ** n) MOD m                   by MOD_MOD, MOD_TIMES2, 0 < m
      = (a ** SUC n) MOD m                   by EXP
*)
val exp_mod_binary_eqn = store_thm(
  "exp_mod_binary_eqn",
  ``!m n a. exp_mod_binary a n m = a ** n MOD m``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[Once exp_mod_binary_def] >>
  Cases_on `m = 1` >-
  rw[Once exp_mod_binary_def] >>
  `1 < m /\ 0 < m` by decide_tac >>
  Induct_on `n` >-
  simp[exp_mod_binary_0, ONE_MOD, EXP] >>
  metis_tac[exp_mod_binary_suc, MOD_MOD, MOD_TIMES2, EXP]);

(* Another proof of the same result *)

(* Theorem: exp_mod_binary a n m = (a ** n) MOD m *)
(* Proof:
   If m = 0, true trivially                  by exp_mod_binary_def
   If m = 1,
        exp_mod_binary a n m
      = 1                                    by exp_mod_binary_def
      = (a ** n) MOD 1                       by MOD_1
   If m <> 0 and m <> 1,
   Then 1 < m.
   By complete induction on n.
   Assume: !j. j < n ==> !a. exp_mod_binary a j m = a ** j MOD m
   To show: exp_mod_binary a n m = a ** n MOD m
   If n = 0,
        exp_mod_binary a 0 m
      = 1                        by exp_mod_binary_0
      = 1 MOD m                  by ONE_MOD, 1 < m
      = (a ** 0) MOD m           by EXP
   If n <> 0,
      Then HALF n < n            by HALF_LT
      If EVEN n,
         Then n MOD 2 = 0        by EVEN_MOD2
           exp_mod_binary a n m
         = exp_mod_binary ((a * a) MOD m) (HALF n) m   by exp_mod_binary_def, n MOD 2 = 0
         = exp_mod_binary ((a ** 2) MOD m) (HALF n) m  by EXP_2
         = (((a ** 2) MOD m) ** (HALF n)) MOD m        by induction hypothesis, HALF n < n
         = ((a ** 2) ** (HALF n)) MOD m                by EXP_MOD, 0 < m
         = (a ** (2 * HALF n)) MOD m                   by EXP_EXP_MULT
         = (a ** n) MOD m                              by EVEN_HALF
      If ~EVEN n,
        Then ODD n                                     by ODD_EVEN
           exp_mod_binary a n m
         = (a * exp_mod_binary ((a * a) MOD m) (HALF n) m) MOD m    by exp_mod_binary_def, n MOD 2 <> 0
         = (a * exp_mod_binary ((a ** 2) MOD m) (HALF n) m) MOD m   by EXP_2
         = (a * (((a ** 2) MOD m) ** (HALF n)) MOD m) MOD m         by induction hypothesis, HALF n < n
         = (a * ((a ** 2) ** (HALF n)) MOD m) MOD m                 by EXP_MOD, 0 < m
         = (a * (a ** (2 * HALF n)) MOD m) MOD m                    by EXP_EXP_MULT
         = (a * a ** (2 * HALF n)) MOD m                            by MOD_TIMES2, 0 < m
         = (a ** (1 + 2 * HALF n)) MOD m                            by EXP_ADD
         = (a ** (2 * HALF n + 1)) MOD m                            by arithmetic
         = (a ** n) MOD m                                           by ODD_HALF
*)
val exp_mod_binary_eqn = store_thm(
  "exp_mod_binary_eqn",
  ``!m n a. exp_mod_binary a n m = (a ** n) MOD m``,
  ntac 2 strip_tac >>
  Cases_on `m = 0` >-
  rw[Once exp_mod_binary_def] >>
  Cases_on `m = 1` >-
  rw[Once exp_mod_binary_def] >>
  `1 < m /\ 0 < m` by decide_tac >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[exp_mod_binary_0, EXP] >>
  `0 < m` by decide_tac >>
  `HALF n < n` by rw[HALF_LT] >>
  rw[Once exp_mod_binary_def] >| [
    `((a ** 2) ** HALF n) MOD m = (a ** (2 * HALF n)) MOD m` by rw[EXP_EXP_MULT] >>
    `_ = (a ** n) MOD m` by rw[GSYM EVEN_HALF, EVEN_MOD2] >>
    rw[],
    `ODD n` by rw[ODD_EVEN] >>
    `(a * (a ** 2) ** HALF n) MOD m = (a * (a ** (2 * HALF n) MOD m)) MOD m` by rw[EXP_EXP_MULT] >>
    `_ = (a * a ** (2 * HALF n)) MOD m` by metis_tac[MOD_TIMES2, MOD_MOD] >>
    `_ = (a ** (2 * HALF n + 1)) MOD m` by rw[EXP_ADD] >>
    `_ = a ** n MOD m` by metis_tac[ODD_HALF] >>
    rw[]
  ]);

(* Theorem: exp_mod_binary 0 n m = (if n = 0 then 1 else 0) MOD m *)
(* Proof:
     exp_mod_binary 0 n m
   = (0 ** n) MOD m                          by exp_mod_binary_eqn
   = (if n = 0 then 1 else 0) MOD m          by ZERO_EXP
*)
val exp_mod_binary_0_n = store_thm(
  "exp_mod_binary_0_n",
  ``!m n. exp_mod_binary 0 n m = (if n = 0 then 1 else 0) MOD m``,
  rw[exp_mod_binary_eqn, ZERO_EXP]);

(* ------------------------------------------------------------------------- *)
(* Fast Modular Exponentiation                                               *)
(* ------------------------------------------------------------------------- *)

(* Fast Modular Exponentiation -- iterative form *)
(* Pseudo-Code:
   (m ** n) MOD k = r <- 1
                    loop:
                    if (n == 0) return (r MOD k)
                    if (ODD n) r <- (r * m) MOD k
                    n <- HALF n
                    m <- (SQ m) MOD k
                    goto loop
*)

(* Define fast modulo exponentiation *)
val exp_mod_step_def = Define`
    exp_mod_step m n k r =
       if k = 0 then (r * m ** n) MOD k
       else if n = 0 then (r MOD k) else
       exp_mod_step ((SQ m) MOD k) (HALF n) k (if EVEN n then r else (r * m) MOD k)
`;
val exp_mod_compute_def = Define`
    exp_mod_compute m n k = exp_mod_step m n k 1
`;

(*
EVAL ``exp_mod_compute 2 10 3``; --> 1024 MOD 3 = 1
EVAL ``exp_mod_compute 3 10 17``; --> 59049 MOD 17 = 8
EVAL ``exp_mod_compute 3 8 19 = (3 ** 8) MOD 19``; --> T
*)

(* Theorem: exp_mod_step m 0 k r = r MOD k *)
(* Proof: by exp_mod_step_def *)
val exp_mod_step_0 = store_thm(
  "exp_mod_step_0",
  ``!m r k. exp_mod_step m 0 k r = r MOD k``,
  rw[Once exp_mod_step_def]);

(* Theorem: exp_mod_step m 1 k r = (r * m) MOD k *)
(* Proof: by exp_mod_step_def *)
val exp_mod_step_1 = store_thm(
  "exp_mod_step_1",
  ``!m r k. exp_mod_step m 1 k r = (r * m) MOD k``,
  rw[Once exp_mod_step_def, Once exp_mod_step_def]);

(* Theorem: exp_mod_step m 2 k r = (r * m * m) MOD k *)
(* Proof:
     exp_mod_step m 2 k r
   = exp_mod_step ((SQ m) MOD k) (HALF 2) k r   by exp_mod_step_def, EVEN 2
   = exp_mod_step ((SQ m) MOD k) 1 r            by arithmetic
   = (r * (SQ m) MOD k) MOD k                   by exp_mod_step_1
   = (r * (SQ m)) MOD k                         by MOD_TIMES2, MOD_MOD
   = (r * (m * m)) MOD k                        by EXP_2
   = (r * m * m) MOD k                          by MULT_ASSOC
*)
val exp_mod_step_2 = store_thm(
  "exp_mod_step_2",
  ``!m r k. exp_mod_step m 2 k r = (r * m * m) MOD k``,
  rw[Once exp_mod_step_def, Once exp_mod_step_def, Once exp_mod_step_def]);

(* Theorem: 0 < k ==> !n. EVEN n ==>
            !m r. exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k r *)
(* Proof:
   if n = 0, HALF 0 = 0          by HALF_EQ_0
      Thus LHS = r MOD k = RHS   by exp_mod_step_def
   If n <> 0, true               by exp_mod_step_def
*)
val exp_mod_step_even = store_thm(
  "exp_mod_step_even",
  ``!k. 0 < k ==> !n. EVEN n ==>
   !m r. exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k r``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  metis_tac[exp_mod_step_def, HALF_EQ_0, NOT_ZERO_LT_ZERO] >>
  rw[Once exp_mod_step_def]);

(* Theorem: 0 < k ==> !n. ODD n ==>
            !m r. exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k ((r * m) MOD k) *)
(* Proof:
   Note ODD n ==> ~EVEN n     by ODD_EVEN
               and m <> 0     by EVEN
   The result follows         by exp_mod_step_def
*)
val exp_mod_step_odd = store_thm(
  "exp_mod_step_odd",
  ``!k. 0 < k ==> !n. ODD n ==>
   !m r. exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k ((r * m) MOD k)``,
  rpt strip_tac >>
  `~EVEN n /\ n <> 0` by metis_tac[ODD_EVEN, EVEN] >>
  rw[Once exp_mod_step_def]);

(* Theorem: exp_mod_step m n k r = (r * m ** n) MOD k *)
(* Proof:
   If k = 0, true                            by exp_mod_step_def
   If k <> 0, 0 < k                          by NOT_ZERO_LT_ZERO
   By complete induction on n.
   if n = 0,
        exp_mod_step m 0 k r
      = r MOD k                              by exp_mod_step_0
      = (r * 1) MOD k                        by MULT_RIGHT_1
      = (r * m ** 0) MOD k                   by EXP_0
   If n <> 0,
      then HALF n < n                        by HALF_LT, 0 < n
   If EVEN n,
        exp_mod_step m n k r
      = exp_mod_step ((SQ m) MOD k) (HALF n) k r     by exp_mod_step_even
      = (r * ((SQ m) MOD k) ** (HALF n)) MOD k       by induction hypothesis, HALF n < n
      = (r * (SQ m) ** (HALF n)) MOD k               by EXP_MOD, MOD_TIMES2, MOD_MOD, 0 < k
      = (r * m ** n) MOD k                           by EXP_EVEN
   If ~EVEN n,
      then ODD n                                     by EVEN_ODD
        exp_mod_step m n k r
      = exp_mod_step ((SQ m) MOD k) (HALF n) k ((r * m) MOD k)     by exp_mod_step_odd
      = (((r * m) MOD k) * (((SQ m) MOD k) ** (HALF n))) MOD k     by induction hypothesis, HALF n < n
      = ((r * m) * (SQ m) ** (HALF n)) MOD k         by EXP_MOD, MOD_TIMES2, MOD_MOD, 0 < k
      = (r * (m * (SQ m) ** (HALF n))) MOD k         by MULT_ASSOC
      = (r * m ** n) MOD k                           by EXP_ODD
*)
val exp_mod_step_eqn = store_thm(
  "exp_mod_step_eqn",
  ``!m n k r. exp_mod_step m n k r = (r * m ** n) MOD k``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[Once exp_mod_step_def] >>
  `0 < k` by decide_tac >>
  qid_spec_tac `r` >>
  qid_spec_tac `n` >>
  qid_spec_tac `m` >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[exp_mod_step_0] >>
  `HALF n < n` by rw[] >>
  Cases_on `EVEN n` >| [
    `exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k r` by rw[exp_mod_step_even] >>
    `_ = (r * ((SQ m) MOD k) ** (HALF n)) MOD k` by rw[] >>
    `_ = (r * (SQ m) ** (HALF n)) MOD k` by rw[Once EXP_MOD] >>
    `_ = (r * m ** n) MOD k` by rw[GSYM EXP_EVEN] >>
    rw[],
    `ODD n` by rw[ODD_EVEN] >>
    `exp_mod_step m n k r = exp_mod_step ((SQ m) MOD k) (HALF n) k (r * m) MOD k` by rw[exp_mod_step_odd] >>
    `_ = (((r * m) MOD k) * (((SQ m) MOD k) ** (HALF n))) MOD k` by rw[] >>
    `_ = ((r * m) * (SQ m) ** (HALF n)) MOD k` by rw[Once EXP_MOD] >>
    `_ = (r * (m * (SQ m) ** (HALF n))) MOD k` by rw[] >>
    `_ = (r * m ** n) MOD k` by rw[EXP_ODD] >>
    rw[]
  ]);

(* Theorem: exp_mod_compute m 0 k = 1 MOD k *)
(* Proof:
     exp_mod_compute m 0 k
   = exp_mod_step m 0 k 1   by exp_mod_compute_def
   = 1 MOD k                by exp_mod_step_0
*)
val exp_mod_compute_0 = store_thm(
  "exp_mod_compute_0",
  ``!m k. exp_mod_compute m 0 k = 1 MOD k``,
  rw[exp_mod_compute_def, exp_mod_step_0]);

(* Theorem: exp_mod_compute m 1 k = m MOD k *)
(* Proof:
     exp_mod_compute m 1 k
   = exp_mod_step m 1 k 1   by exp_mod_compute_def
   = (1 * m) MOD k          by exp_mod_step_1
   = m MOD k                by MULT_LEFT_1
*)
val exp_mod_compute_1 = store_thm(
  "exp_mod_compute_1",
  ``!m k. exp_mod_compute m 1 k = m MOD k``,
  rw[exp_mod_compute_def, exp_mod_step_1]);

(* Theorem: exp_mod_compute m 2 k = (SQ m) MOD k *)
(* Proof:
     exp_mod_compute m 2 k
   = exp_mod_step m 2 k 1   by exp_mod_compute_def
   = (1 * n * n) MOD k      by exp_mod_step_2
   = (SQ m) MOD k           by EXP_2
*)
val exp_mod_compute_2 = store_thm(
  "exp_mod_compute_2",
  ``!m k. exp_mod_compute m 2 k = (SQ m) MOD k``,
  rw[exp_mod_compute_def, exp_mod_step_2]);

(* Theorem: 0 < k ==> !n. EVEN n ==>
            !m. exp_mod_compute m n k = exp_mod_compute ((SQ m) MOD k) (HALF n) k *)
(* Proof:
     exp_mod_compute m n k
   = exp_mod_step m n k 1                       by exp_mod_compute_def
   = exp_mod_step ((SQ m) MOD k) (HALF n) k 1   by exp_mod_step_even, EVEN n
   = exp_mod_compute ((SQ m) MOD k) (HALF n) k  by exp_mod_compute_def
*)
val exp_mod_compute_even = store_thm(
  "exp_mod_compute_even",
  ``!k. 0 < k ==> !n. EVEN n ==>
   !m. exp_mod_compute m n k = exp_mod_compute ((SQ m) MOD k) (HALF n) k``,
  rw[exp_mod_compute_def, exp_mod_step_even]);

(* Theorem: 0 < k ==> !n. ODD n ==>
            !m. exp_mod_compute m n k = exp_mod_step ((SQ m) MOD k) (HALF n) k (m MOD k) *)
(* Proof:
     exp_mod_compute m n k
   = exp_mod_step m n k 1                                   by exp_mod_compute_def
   = exp_mod_step ((SQ m) MOD k) (HALF n) k (1 * m MOD k)   by exp_mod_step_odd, ODD n
   = exp_mod_step ((SQ m) MOD k) (HALF n) k (m MOD k)       by MULT_LEFT_1
*)
val exp_mod_compute_odd = store_thm(
  "exp_mod_compute_odd",
  ``!k. 0 < k ==> !n. ODD n ==>
   !m. exp_mod_compute m n k = exp_mod_step ((SQ m) MOD k) (HALF n) k (m MOD k)``,
  rw[exp_mod_compute_def, exp_mod_step_odd]);

(* Theorem: exp_mod_compute m n k = (m ** n) MOD k *)
(* Proof:
     exp_mod_compute m n k
   = exp_mod_step m n k 1     by exp_mod_compute_def
   = (1 * m ** n) MOD k       by exp_mod_step_eqn
   = (m ** n) MOD k           by MULT_LEFT_1
*)
val exp_mod_compute_eqn = store_thm(
  "exp_mod_compute_eqn",
  ``!m n k. exp_mod_compute m n k = (m ** n) MOD k``,
  rw[exp_mod_compute_def, exp_mod_step_eqn]);

(* ------------------------------------------------------------------------- *)
(* ROOT computation                                                          *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: n r
Output: ROOT r n = r-th root of n.

Make use of indentity:
n ^ (1/r) = 2 (n/ 2^r) ^(1/r)

if n = 0 then 0
else (* precompute *) let x = 2 * r-th root of (n DIV (2 ** r))
     (* apply *) in if n < (SUC x) ** r then x else (SUC x)
*)


(* Define root computation by root identity *)
Definition root_compute_def:
  root_compute r n =
  if 0 < r then
     if n = 0 then 0
     else (let x = 2 * root_compute r (n DIV (exp_compute 2 r)) in
           if n < exp_compute (SUC x) r then x else (SUC x))
  else ROOT 0 n
Termination
  WF_REL_TAC `measure SND` >> rw[] >>
  `1 < 2 ** r` by rw[ONE_LT_EXP] >>
  rw[exp_compute_eqn, DIV_LESS]
End

(*
> EVAL ``root_compute 3 0``; --> 0
> EVAL ``root_compute 3 2``; --> 1
> EVAL ``root_compute 3 3``; --> 1
> EVAL ``root_compute 3 7``; --> 1
> EVAL ``root_compute 3 8``; --> 2
> EVAL ``root_compute 3 10``; --> 2
> EVAL ``root_compute 3 20``; --> 2
> EVAL ``root_compute 3 27``; --> 3
> EVAL ``root_compute 3 26``; --> 2
> EVAL ``root_compute 3 28``; --> 3
> EVAL ``root_compute 3 63``; --> 3
> EVAL ``root_compute 3 64``; --> 4
> EVAL ``root_compute 3 65``; --> 4
*)

(* Theorem: root_compute r n =
      if 0 < r then if n = 0 then 0 else (let x = 2 * root_compute r (n DIV (2 ** r))
                                           in if n < (SUC x) ** r then x else (SUC x))
               else ROOT 0 n *)
(* Proof: by root_compute_def, exp_compute_eqn *)
val root_compute_alt = store_thm(
  "root_compute_alt",
  ``!r n. root_compute r n = if 0 < r then
                            if n = 0 then 0 else
                               (let x = 2 * root_compute r (n DIV (2 ** r))
                                 in if n < (SUC x) ** r then x else (SUC x))
                            else ROOT 0 n``,
  rw[Once root_compute_def, exp_compute_eqn]);

(* Theorem: root_compute r 0 = 0 *)
(* Proof: by root_compute_def *)
val root_compute_0 = store_thm(
  "root_compute_0",
  ``!r. 0 < r ==> (root_compute r 0 = 0)``,
  rw[Once root_compute_def]);

(* Theorem: root_compute 1 n = n *)
(* Proof:
   By complete induction on n.
   Assume !m. m < n ==> (root_compute 1 m = m)
   To show: root_compute 1 n = n

   Note HALF n < n       by HALF_LT, 0 < n

     root_compute 1 n
   = let x = 2 * root_compute 1 (n DIV (2 ** 1))
      in if n < (SUC x) ** 1 then x else (SUC x)   by root_compute_alt
   = let x = 2 * root_compute 1 (HALF n)
      in if n < SUC x then x else SUC x            by simplification, EXP_1
   = let x = 2 * HALF n
     in if n < SUC x then x else SUC x             by induction hypothesis
   = if n < SUC (2 * HALF n) then (2 * HALF n) else SUC (2 * HALF n)

   If EVEN n,
      Then n = 2 * HALF n          by EVEN_HALF
      Since n < SUC n              by LESS_SUC
        root_compute 1 n
      = 2 * HALF n                 by above
      = n                          by EVEN_HALF
   If ~(EVEN n), then ODD n        by EVEN_ODD
      Then n = SUC (2 * HALF n)    by ODD_HALF, ADD1
        or n < SUC (2 * HALF n) = F
        root_compute 1 n
      = SUC (2 * HALF n)           by above
      = n                          by ODD_HALF
*)
val root_compute_1 = store_thm(
  "root_compute_1",
  ``!n. root_compute 1 n = n``,
  completeInduct_on `n` >>
  rw[Once root_compute_alt] >| [
    spose_not_then strip_assume_tac >>
    `ODD n` by metis_tac[EVEN_HALF, ODD_EVEN] >>
    `n = SUC (2 * HALF n)` by metis_tac[ODD_HALF, ADD1] >>
    decide_tac,
    spose_not_then strip_assume_tac >>
    `EVEN n` by metis_tac[ODD_HALF, ADD1, EVEN_ODD] >>
    `n = 2 * HALF n` by rw[EVEN_HALF] >>
    decide_tac
  ]);

(* Theorem: root_compute r n = ROOT r n *)
(* Proof:
   If r = 0, true by         by root_compute_alt
   If r <> 0, then 0 < r.
   By complete induction on n.
   Assume: !m. m < n ==> (root_compute r m = ROOT r m)
   To show: root_compute r n = ROOT r n

   If n = 0,
        root_compute r 0
      = 0                    by root_compute_0
      = ROOT r 0             by ROOT_COMPUTE
   If n <> 0,
      Note 1 < 2 ** r        by ONE_LT_EXP, 0 < r
      Thus n DIV 2 ** r < n  by DIV_LESS, 0 < n
      This makes the induction hypothesis applicable for m = n DIV 2 ** r.
      Let x = 2 * ROOT r (n DIV 2 ** r).

        root_compute r n
      = if n < SUC x ** r then x else SUC x    by root_compute_alt, induction hypothesis
      = ROOT r n                               by ROOT_COMPUTE
*)
val root_compute_eqn = store_thm(
  "root_compute_eqn",
  ``!r n. root_compute r n = ROOT r n``,
  rpt strip_tac >>
  Cases_on `r = 0` >-
  rw[Once root_compute_alt] >>
  `0 < r` by decide_tac >>
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw[root_compute_0, ROOT_COMPUTE] >>
  `1 < 2 ** r` by rw[ONE_LT_EXP] >>
  `n DIV 2 ** r < n` by rw[DIV_LESS] >>
  qabbrev_tac `x = 2 * ROOT r (n DIV 2 ** r)` >>
  rw[Once root_compute_alt] >| [
    `ROOT r n = x` by rw[Once ROOT_COMPUTE, Abbr`x`] >>
    decide_tac,
    `ROOT r n = SUC x` by rw[Once ROOT_COMPUTE, Abbr`x`] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Square Root Computation                                                   *)
(* ------------------------------------------------------------------------- *)

(* Overload square-root *)
val _ = overload_on("sqrt_compute", ``root_compute 2``);

(* Theorem: sqrt_compute n = SQRT n *)
(* Proof: by root_compute_eqn *)
val sqrt_compute_eqn = store_thm(
  "sqrt_compute_eqn",
  ``!n. sqrt_compute n = SQRT n``,
  rw[root_compute_eqn]);

(*
> EVAL ``sqrt_compute 1``; --> 1
> EVAL ``sqrt_compute 2``; --> 1
> EVAL ``sqrt_compute 3``; --> 1
> EVAL ``sqrt_compute 4``; --> 2
> EVAL ``sqrt_compute 16``; --> 4
> EVAL ``sqrt_compute 121``; --> 11
> EVAL ``sqrt_compute 1024``; --> 32
*)

(* ------------------------------------------------------------------------- *)
(* Power Free Test                                                           *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode for power-free check.

Input: n
Output: true if the only way to write n = b ** c is b = n , c = 1.

c <- 2
while (c <= LOG2 n) {
    b <- root n c
    if (exp b c = n) return (b, c)
    c <- c + 1
}
or:
c <- 2
while (c <= ulog n) {
    b <- root n c
    if (exp b c = n) return (b, c)
    c <- c + 1
}

The following theorems guarantee that exit must occur within the while-loop.

perfect_power_bound_LOG2;
|- !n. 1 < n ==> !m. perfect_power n m <=> ?k. k <= LOG2 n /\ (n = m ** k)
perfect_power_bound_ulog;
|- !n. 0 < n ==> !m. perfect_power n m <=> ?k. k <= ulog n /\ (n = m ** k)
*)

(* Define power-index computation, search downwards from k = LOG2 n *)
val power_index_compute_def = Define`
    power_index_compute n k =
       if k <= 1 then 1
       else if exp_compute (root_compute k n) k = n then k
       else power_index_compute n (k - 1)
`;

(*
> EVAL ``power_index_compute 8 (log_compute 8)``; --> 3
> EVAL ``power_index_compute 7 (log_compute 7)``; --> 1
> EVAL ``power_index_compute 9 (log_compute 9)``; --> 2
> EVAL ``power_index_compute 10 (log_compute 10)``; --> 1
> EVAL ``power_index_compute 1024 (log_compute 1024)``; --> 10
*)

(* Theorem: power_index_compute n k =
            if k <= 1 then 1 else if (ROOT k n) ** k = n then k else power_index_compute n (k - 1) *)
(* Proof: by power_index_compute_def, root_compute_eqn, exp_compute_eqn *)
val power_index_compute_alt = store_thm(
  "power_index_compute_alt",
  ``!n k. power_index_compute n k =
         if k <= 1 then 1 else if (ROOT k n) ** k = n then k else power_index_compute n (k - 1)``,
  rw[Once power_index_compute_def, root_compute_eqn, exp_compute_eqn]);

(* Theorem: power_index_compute n k = power_index n k *)
(* Proof:
   By complete induction on k.
   Expand by power_index_compute_alt, this is to show:
   (1) k <= 1 ==> 1 = power_index n k
       Note k = 0 or k = 1             by k <= 1
        and power_index n 0 = 1        by power_index_0
        and power_index n 1 = 1        by power_index_1
   (2) ~(k <= 1) /\ ROOT k n ** k = n ==> k = power_index n k
       That is 1 < k                   by ~(k <= 1)
       Thus power_index n k = k        by power_index_exact_root, 0 < k
   (3) ROOT k n ** k <> n ==> power_index_compute n (k - 1) = power_index n k
         power_index_compute n (k - 1)
       = power_index n (k - 1)         by induction hypothesis, k - 1 < k
       = power_index n k               by power_index_not_exact_root
*)
val power_index_compute_eqn = store_thm(
  "power_index_compute_eqn",
  ``!n k. power_index_compute n k = power_index n k``,
  completeInduct_on `k` >>
  rw[Once power_index_compute_alt] >-
  metis_tac[power_index_0, power_index_1, DECIDE``k <= 1 <=> (k = 0) \/ (k = 1)``] >-
  rw[power_index_exact_root] >>
  rw[power_index_not_exact_root]);

(* Define power-free check *)
val power_free_check_def = Define`
    power_free_check n <=> (1 < n) /\ (power_index_compute n (ulog_compute n) = 1)
`;

(*
> EVAL ``power_free_check 6``; --> T
> EVAL ``power_free_check 7``; --> T
> EVAL ``power_free_check 8``; --> F
> EVAL ``power_free_check 9``; --> F
> EVAL ``power_free_check 10``; --> T
> EVAL ``power_free_check 26``; --> T
> EVAL ``power_free_check 27``; --> F
> EVAL ``power_free_check 127``; --> T
> EVAL ``power_free_check 128``; --> F
> EVAL ``power_free_check 0``; --> F
> EVAL ``power_free_check 1``; --> F
> EVAL ``power_free_check 2``; --> T
*)

(* Theorem: power_free_check 0 <=> F *)
(* Proof: by power_free_check_def *)
val power_free_check_0 = store_thm(
  "power_free_check_0",
  ``power_free_check 0 <=> F``,
  rw[power_free_check_def]);

(* Theorem: power_free_check 1 <=> F *)
(* Proof: by power_free_check_def *)
val power_free_check_1 = store_thm(
  "power_free_check_1",
  ``power_free_check 1 <=> F``,
  rw[power_free_check_def]);

(* Theorem: power_free_check n <=> (1 < n) /\ (power_index n (ulog n) = 1) *)
(* Proof: by power_free_check_def, power_index_compute_eqn, ulog_compute_eqn *)
val power_free_check_alt = store_thm(
  "power_free_check_alt",
  ``!n. power_free_check n <=> (1 < n) /\ (power_index n (ulog n) = 1)``,
  rw[power_free_check_def, power_index_compute_eqn, ulog_compute_eqn]);

(* Theorem: power_free_check n <=> power_free n *)
(* Proof: by power_free_check_alt, power_free_by_power_index_ulog *)
val power_free_check_eqn = store_thm(
  "power_free_check_eqn",
  ``!n. power_free_check n <=> power_free n``,
  rw[power_free_check_alt, power_free_by_power_index_ulog]);

(* Theorem: power_free n <=> power_free_check n *)
(* Proof: by power_free_check_eqn *)
val power_free_eval = store_thm(
  "power_free_eval[compute]",
  ``!n. power_free n <=> power_free_check n``,
  rw[power_free_check_eqn]);

(*
> EVAL ``power_free 0``; = F
> EVAL ``power_free 1``; = F
> EVAL ``power_free 2``; = T
> EVAL ``power_free 3``; = T
> EVAL ``power_free 4``; = F
> EVAL ``power_free 5``; = T
> EVAL ``power_free 6``; = T
> EVAL ``power_free 7``; = T
> EVAL ``power_free 8``; = F
> EVAL ``power_free 9``; = F
*)

(* Theorem alias *)
val power_free_check_by_ulog = save_thm("power_free_check_by_ulog", power_free_check_alt);
(* val power_free_check_by_ulog =
   |- !n. power_free_check n <=> 1 < n /\ (power_index n (ulog n) = 1): thm *)

(* Theorem: power_free_check n <=> (1 < n) /\ (power_index n (LOG2 n) = 1) *)
(* Proof: by power_free_check_eqn, power_free_by_power_index_LOG2 *)
val power_free_check_by_LOG2 = store_thm(
  "power_free_check_by_LOG2",
  ``!n. power_free_check n <=> (1 < n) /\ (power_index n (LOG2 n) = 1)``,
  rw[power_free_check_eqn, power_free_by_power_index_LOG2]);

(* ------------------------------------------------------------------------- *)
(* GCD computation                                                          *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: n m
Output: gcd n m

Recursive version:

if (n = m) return n      // gcd n n = n
if (n = 0) return m      // gcd 0 m = m
if (m = 0) return n      // gcd n 0 = n

if ~(n < m) return gcd m n   // gcd n m = gcd m n, ensure first < second.

if (EVEN n) then
   if (EVEN m) then return 2 * (gcd (HALF n) (HALF m))  // because 2 is a common divisor.
               else return gcd (HALF n) m               // because 2 is not a common divisor.
else
   if (EVEN m) then return gcd n (HALF m)               // because 2 is not a common divisor.
               else return gcd n (HALF (m - n))         // because (m - n) is EVEN, as both are ODD.

Iterative version:

if (n = 0) return m      // gcd 0 m = m
if (m = 0) return n      // gcd n 0 = n

// Let shift k := log K, where K is the greatest power of 2 dividing both n and m.
k <- 0            // initialize shift
while (EVEN n) and (EVEN m) {
   k <- k + 1     // increment shift
   n <- HALF n
   m <- HALF m
}

// remove all factors of 2 in n -- they are not common.
 while (EVEN n) n <- HALF n

// From here on, n is always odd.
do {
   // remove all factors of 2 in m -- they are not common.
   // note: m is not zero, so while will terminate.
   while (EVEN m) m <- HALF m

   // Now n and m are both odd. Swap if necessary so n <= m,
   // then set m = m - n (which is even).
   if (n > m) swap (n, m)    // ensure n <= m
   m <- m - n                // set EVEN m
} while (m != 0)

return n * (2 ** k)          // restore common factors of 2

*)

(* Proof in gcd theory:

val BINARY_GCD = store_thm("BINARY_GCD",
  ``!m n.
      (EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (m DIV 2) (n DIV 2))) /\
      (EVEN m /\ ODD n ==> (gcd m n = gcd (m DIV 2) n))``,
  SIMP_TAC bool_ss [EVEN_EXISTS] THEN REVERSE (REPEAT STRIP_TAC)
  THEN `0 < 2` by (MATCH_MP_TAC PRIME_POS THEN REWRITE_TAC [PRIME_2])
  THEN FULL_SIMP_TAC bool_ss [GCD_COMMON_FACTOR,
         ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,
         ONCE_REWRITE_RULE [GCD_SYM] ODD_IMP_GCD_CANCEL_EVEN]);
*)

(* Rework the proof of BINARY_GCD in gcd theory. *)

(* Theorem: ODD n ==> (gcd n (2 * m) = gcd n m) *)
(* Proof:
   Since ODD n, 2 cannot be the common divisor of n and (2 * m).
   Therefore, any common divisor d of n and (2 * m) divides n and m,
   or gcd n m = gcd n (2 * m)

   Let a = gcd n (2 * m), b = gcd n m.

   Step 1: show !c. c divides n /\ c divides (2 * m) ==> c divides m
      Claim coprime 2 c.
      Proof: Let d = gcd 2 c.
             Then d divides 2 /\ d divides c  by GCD_IS_GREATEST_COMMON_DIVISOR
               so d <= 2                      by DIVIDES_LE, 0 < 2
              and d <> 0                      by ZERO_DIVIDES, 2 <> 0
             Note ODD n ==> ODD c             by DIVIDES_ODD, c divides n
             Thus d <> 2                      by DIVIDES_MOD_0, ODD_MOD2
               or d = 1                       by arithmetic
      Then c divides m                        by L_EUCLIDES, coprime 2 c /\ c divides (2 * m).

   Step 2: show a divides b
      Note a divides n /\ a divides (2 * m)   by GCD_IS_GREATEST_COMMON_DIVISOR
        or a divides n /\ a divides m         by Step 1
        so a divides gcd n m = b              by GCD_IS_GREATEST_COMMON_DIVISOR

   Step 3: show b divides a
      Note b divides n /\ b divides m         by GCD_IS_GREATEST_COMMON_DIVISOR
        or b divides n /\ b divides (2 * m)   by DIVIDES_MULTIPLE
        or b divides gcd n (2 * m) = a        by GCD_IS_GREATEST_COMMON_DIVISOR

   Since a divides b /\ b divides a, a = b    by DIVIDES_ANTISYM
*)
val ODD_IMP_GCD_CANCEL_EVEN = store_thm(
  "ODD_IMP_GCD_CANCEL_EVEN",
  ``!m n. ODD n ==> (gcd n (2 * m) = gcd n m)``,
  rpt strip_tac >>
  qabbrev_tac `a = gcd n (2 * m)` >>
  qabbrev_tac `b = gcd n m` >>
  `!c. c divides n /\ c divides (2 * m) ==> c divides m` by
  (rpt strip_tac >>
  `coprime 2 c` by
    (qabbrev_tac `d = gcd 2 c` >>
  `d divides 2 /\ d divides c` by rw[GCD_IS_GREATEST_COMMON_DIVISOR, Abbr`d`] >>
  `d <= 2` by rw[DIVIDES_LE] >>
  `d <> 0` by metis_tac[ZERO_DIVIDES, DECIDE``2 <> 0``] >>
  `d <> 2` by metis_tac[DIVIDES_ODD, DIVIDES_MOD_0, ODD_MOD2, DECIDE``1 <> 0 /\ 0 < 2``] >>
  decide_tac) >>
  metis_tac[L_EUCLIDES]) >>
  metis_tac[GCD_IS_GREATEST_COMMON_DIVISOR, DIVIDES_MULTIPLE, DIVIDES_ANTISYM]);

(* Proof in gcd theory:

val ODD_IMP_GCD_CANCEL_EVEN = prove(
  ``!n. ODD n ==> (gcd n (2 * m) = gcd n m)``,
  REPEAT STRIP_TAC
  THEN MATCH_MP_TAC GCD_CANCEL_MULT
  THEN ONCE_REWRITE_TAC [GCD_SYM]
  THEN REVERSE (`~divides 2 n` by ALL_TAC)
  THEN1 (MP_TAC (Q.SPEC `n` (MATCH_MP PRIME_GCD PRIME_2))
         THEN ASM_REWRITE_TAC [])
  THEN REWRITE_TAC [divides_def]
  THEN ONCE_REWRITE_TAC [MULT_COMM]
  THEN REWRITE_TAC [GSYM EVEN_EXISTS]
  THEN FULL_SIMP_TAC bool_ss [ODD_EVEN]);
*)

(* Theorem: (EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (HALF m) (HALF n))) /\
            (EVEN m /\ ODD n ==> (gcd m n = gcd (HALF m) n)) *)
(* Proof:
   This is to show:
   (1) EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (HALF m) (HALF n))
       Let hm = HALF m, then m = 2 * hm      by EVEN_HALF
       Let hn = HALF n, then n = 2 * hn      by EVEN_HALF
           gcd m n
         = gcd (2 * hm) (2 * hn)             by above
         = 2 * gcd hm hn                     by GCD_COMMON_FACTOR
   (2) EVEN m /\ ODD n ==> (gcd m n = gcd (HALF m) n)
       Let hm = HALF m, then m = 2 * hm      by EVEN_HALF
           gcd m n
         = gcd (2 * hm) n                    by above
         = gcd n (2 * hm)                    by GCD_SYM
         = gcd n hm                          by ODD_IMP_GCD_CANCEL_EVEN
         = gcd hm n                          by GCD_SYM
*)
val BINARY_GCD = store_thm(
  "BINARY_GCD",
  ``!m n. (EVEN m /\ EVEN n ==> (gcd m n = 2 * gcd (HALF m) (HALF n))) /\
         (EVEN m /\ ODD n ==> (gcd m n = gcd (HALF m) n))``,
  rpt strip_tac >-
  metis_tac[EVEN_HALF, GCD_COMMON_FACTOR] >>
  metis_tac[EVEN_HALF, ODD_IMP_GCD_CANCEL_EVEN, GCD_SYM]);

(* Note: For ODD m /\ ODD n,
   Let n < m, then apply GCD_SUB_L:  gcd m n = gcd (m - n) n,  with EVEN (m - n)
*)

(* Convert BINARY_GCD into an algorithm *)
val gcd_compute_def = Define`
    gcd_compute n m =
       if n = 0 then m
     else if m = 0 then n
     else if n = m then n
     else (* n <> m *)
       if EVEN n then if EVEN m then 2 * gcd_compute (HALF n) (HALF m)
                 else (* ODD m *) gcd_compute (HALF n) m
     else (* ODD n *) if EVEN m then gcd_compute n (HALF m)
                 else (* ODD m *)
                   if n < m then gcd_compute n (m - n) else gcd_compute (n - m) m
`;
(* Techniques for recursive definition:
(1) Keep the parameter order for recursive calls (no swapping of parameter).
(2) Provide exit conditions for small enough parameters.
(3) If possible, keep the parameters decreasing:
    with luck, termination proof is automatic!
*)

(*
> EVAL ``gcd_compute 6 9``; --> 3
> EVAL ``gcd_compute 6 8``; --> 2
> EVAL ``gcd_compute 6 7``; --> 1
> EVAL ``gcd_compute 6 6``; --> 6
> EVAL ``gcd_compute 6 5``; --> 1
> EVAL ``gcd_compute 6 4``; --> 2
> EVAL ``gcd_compute 6 3``; --> 3
> EVAL ``gcd_compute 6 2``; --> 2
> EVAL ``gcd_compute 6 1``; --> 1
> EVAL ``gcd_compute 6 0``; --> 6
*)

(* Theorem: (gcd_compute 0 n = n) /\ (gcd_compute n 0 = n) *)
(* Proof: by gcd_compute_def *)
val gcd_compute_0 = store_thm(
  "gcd_compute_0",
  ``!n. (gcd_compute 0 n = n) /\ (gcd_compute n 0 = n)``,
  rw[Once gcd_compute_def] >>
  rw[Once gcd_compute_def]);

(* Theorem: gcd_compute n n = n *)
(* Proof: by gcd_compute_def *)
val gcd_compute_id = store_thm(
  "gcd_compute_id",
  ``!n. gcd_compute n n = n``,
  rw[Once gcd_compute_def]);

(* Theorem: EVEN n /\ EVEN m ==> (gcd_compute n m = 2 * gcd_compute (HALF n) (HALF m)) *)
(* Proof:
   If n = m,
      Then HALF n = HALF m,
        so gcd_compute n m = n                      by gcd_compute_id
       and gcd_compute (HALF n) (HALF m) = HALF n   by gcd_compute_id
      Thus result is true                           by EVEN_HALF
   If n <> m,
      Note EVEN 0                                   by EVEN
       and HALF 0 = 0                               by ZERO_DIV
        If n = 0,
           gcd_compute 0 m = m                      by gcd_compute_0
           gcd_compute (HALF 0) (HALF m) = HALF m   by gcd_compute_0
           Thus result is true                      by EVEN_HALF, EVEN m
        If m = 0,
           gcd_compute n 0 = n                      by gcd_compute_0
           gcd_compute (HALF n) (HALF 0) = HALF n   by gcd_compute_0
           Thus result is true                      by EVEN_HALF, EVEN n
        If n <> 0 and m <> 0,
           The result is true                       by gcd_compute_def
*)
val gcd_compute_even_even = store_thm(
  "gcd_compute_even_even",
  ``!m n. EVEN n /\ EVEN m ==> (gcd_compute n m = 2 * gcd_compute (HALF n) (HALF m))``,
  rpt strip_tac >>
  Cases_on `n = m` >-
  metis_tac[gcd_compute_id, EVEN_HALF] >>
  `EVEN 0 /\ (HALF 0 = 0)` by rw[] >>
  Cases_on `n = 0` >-
  metis_tac[gcd_compute_0, EVEN_HALF] >>
  Cases_on `m = 0` >-
  metis_tac[gcd_compute_0, EVEN_HALF] >>
  rw[Once gcd_compute_def]);

(* Theorem: EVEN n /\ ODD m ==> (gcd_compute n m = gcd_compute (HALF n) m) *)
(* Proof:
   If n = 0,
      Then HALF 0 = 0                    by ZERO_DIV, 0 < 2
        so gcd_compute 0 m = m           by gcd_compute_0
       and gcd_compute (HALF 0) m = m    by gcd_compute_0
      Thus result is true.
   If n <> 0,
      Note m <> 0                        by ODD
       and ~EVEN m                       by EVEN_ODD
        so n <> m                        by EVEN n, ~EVEN m
      Thus result is true                by gcd_compute_def
*)
val gcd_compute_even_odd = store_thm(
  "gcd_compute_even_odd",
  ``!m n. EVEN n /\ ODD m ==> (gcd_compute n m = gcd_compute (HALF n) m)``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[gcd_compute_0] >>
  `~EVEN m` by rw[GSYM ODD_EVEN] >>
  `n <> m` by metis_tac[] >>
  `m <> 0` by metis_tac[ODD] >>
  rw[Once gcd_compute_def]);

(* Theorem: ODD n /\ EVEN m ==> (gcd_compute n m = gcd_compute n (HALF m)) *)
(* Proof:
   If m = 0,
      Then HALF 0 = 0                    by ZERO_DIV, 0 < 2
        so gcd_compute n 0 = n           by gcd_compute_0
       and gcd_compute n (HALF 0) = n    by gcd_compute_0
      Thus result is true.
   If m <> 0,
      Note n <> 0                        by ODD
       and ~EVEN n                       by EVEN_ODD
        so n <> m                        by EVEN m, ~EVEN n
      Thus result is true                by gcd_compute_def
*)
val gcd_compute_odd_even = store_thm(
  "gcd_compute_odd_even",
  ``!m n. ODD n /\ EVEN m ==> (gcd_compute n m = gcd_compute n (HALF m))``,
  rpt strip_tac >>
  Cases_on `m = 0` >-
  rw[gcd_compute_0] >>
  `~EVEN n` by rw[GSYM ODD_EVEN] >>
  `n <> m` by metis_tac[] >>
  `n <> 0` by metis_tac[ODD] >>
  rw[Once gcd_compute_def]);

(* Theorem: ODD n /\ ODD m ==> (gcd_compute n m =
            if n < m then gcd_compute n (m - n) else gcd_compute (n - m) m) *)
(* Proof:
   If n = m,
      Then gcd_compute n n       by gcd_compute_id
       and gcd_compute (n - n) n
         = gcd_compute 0 n       by n - n = 0
         = n                     by gcd_compute_0
      Hence true.
   If n <> m,
      Note ~EVEN n /\ ~EVEN m    by ODD_EVEN
      also n <> 0 /\ m <> 0      by ODD
      The result is true         by gcd_compute_def
*)
val gcd_compute_odd_odd = store_thm(
  "gcd_compute_odd_odd",
  ``!m n. ODD n /\ ODD m ==> (gcd_compute n m =
         if n < m then gcd_compute n (m - n) else gcd_compute (n - m) m)``,
  rpt strip_tac >>
  Cases_on `n = m` >-
  metis_tac[gcd_compute_id, gcd_compute_0, DECIDE``n - n = 0``] >>
  `~EVEN n /\ ~EVEN m` by rw[GSYM ODD_EVEN] >>
  `n <> 0 /\ m <> 0` by metis_tac[ODD] >>
  rw[Once gcd_compute_def]);

(* Theorem: gcd_compute n m = gcd n m *)
(* Proof:
   By complete induction on (n + m).
   Apply gcd_compute_def, this is to show:
   (1) m = gcd 0 m, true                 by GCD_0
   (2) n <> 0 ==> n = gcd n 0, true      by GCD_0
   (3) m <> 0 ==> m = gcd m m            by GCD_REF
   (4) n <> 0 /\ m <> 0 /\ n <> m /\ EVEN n /\ EVEN m ==> 2 * gcd_compute (HALF n) (HALF m) = gcd n m
       Note HALF n < n /\ HALF m < m     by HALF_LT, 0 < n, 0 < m
         so HALF n + HALF m < n + m      by arithmetic
            2 * gcd_compute (HALF n) (HALF m)
          = 2 * gcd (HALF n) (HALF m)    by induction hypothesis
          = gcd n m                      by BINARY_GCD
   (5) n <> 0 /\ m <> 0 /\ n <> m /\ EVEN n /\ ~EVEN m ==> gcd_compute (HALF n) m = gcd n m
       Note HALF n < n                   by HALF_LT, 0 < n
         so HALF n + m < n + m           by arithmetic
        Now ODD m                        by EVEN_ODD
            gcd_compute (HALF n) m
          = gcd (HALF n) m               by induction hypothesis
          = gcd n m                      by BINARY_GCD
   (6) n <> 0 /\ m <> 0 /\ n <> m /\ ~EVEN n /\ EVEN m ==> gcd_compute n (HALF m) = gcd n m
       Note ODD n                        by EVEN_ODD
        and HALF m < m                   by HALF_LT, 0 < m
         so n + HALF m < n + m           by arithmetic
            gcd_compute n (HALF m)
          = gcd n (HALF m)               by induction hypothesis
          = gcd (HALF m) n               by GCD_SYM
          = gcd m n                      by BINARY_GCD
          = gcd n m                      by GCD_SYM
   (7) n <> 0 /\ m <> 0 /\ n <> m /\ ~EVEN n /\ ~EVEN m /\ n < m ==> gcd_compute n (m - n) = gcd n m
       Note n + (m - n) = m              by n < m
         so n + (m - n) < n + m          by 0 < n
            gcd_compute n (m - n)
          = gcd n (m - n)                by induction hypothesis
          = gcd n m                      by GCD_SUB_R, n < m ==> n <= m
   (8) n <> 0 /\ m <> 0 /\ n <> m /\ ~EVEN n /\ ~EVEN m /\ ~(n < m) ==> gcd_compute (n - m) m = gcd n m
       Note m <= n                       by NOT_LESS, ~(n < m)
        and (n - m) + m = n              by m <= n
         so (n - m) + m < n + m          by 0 < m
            gcd_compute (n - m) m
          = gcd (n - m) m                by induction hypothesis
          = gcd n m                      by GCD_SUB_L, m <= n
*)
val gcd_compute_eqn = store_thm(
  "gcd_compute_eqn",
  ``!m n. gcd_compute n m = gcd n m``,
  rpt strip_tac >>
  completeInduct_on `n + m` >>
  rpt strip_tac >>
  rw[Once gcd_compute_def] >| [
    `HALF n < n /\ HALF m < m` by rw[HALF_LT] >>
    `HALF n + HALF m < n + m` by rw[] >>
    rw[BINARY_GCD],
    metis_tac[BINARY_GCD, EVEN_ODD],
    metis_tac[BINARY_GCD, EVEN_ODD, GCD_SYM],
    metis_tac[GCD_SUB_R, LESS_IMP_LESS_OR_EQ],
    metis_tac[GCD_SUB_L, NOT_LESS]
  ]);

(* Theorem: (gcd_compute 1 n = 1) /\ (gcd_compute n 1 = 1) *)
(* Proof: by gcd_compute_eqn, GCD_1 *)
val gcd_compute_1 = store_thm(
  "gcd_compute_1",
  ``!n. (gcd_compute 1 n = 1) /\ (gcd_compute n 1 = 1)``,
  rw_tac std_ss[gcd_compute_eqn, GCD_1]);

(* Theorem: gcd_compute n m = gcd_compute m n *)
(* Proof: gcd_compute_eqn, GCD_SYM *)
val gcd_compute_sym = store_thm(
  "gcd_compute_sym",
  ``!m n. gcd_compute n m = gcd_compute m n``,
  rw[gcd_compute_eqn, GCD_SYM]);

(* ------------------------------------------------------------------------- *)
(* Phi Computation                                                           *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: n
Output: phi n

if (n = 0) return 0 // phi 0 = 0
j <- n              // initial index
c <- 1              // initial count, when j = 1, always coprime j n
while (1 < j) {
   if (coprime j n) c <- c + 1   // increment count if coprime j n
   j <- j - 1                    // decrement j
}
return c           // the result

*)

(* Count the number of coprimes down to 1, accumulator version:
val count_coprime_def = Define `
    count_coprime n j k = (* j = n downto 1, k = count from 0 *)
    if 1 < j then (* decrement j, and update count k depending on coprime j n *)
       count_coprime n (j - 1) (if coprime j n then k + 1 else k)
       else k + 1  (* add the last n = 1, always coprime *)
`;
*)

(* Count the number of coprimes down to 1, stack version
val count_coprime_def = Define `
    count_coprime n j = (* j = n downto 1, return count from 1 *)
    if 1 < j then (* decrement j, and update count k depending on coprime j n *)
       count_coprime n (j - 1) + (if (gcd_compute j n = 1) then 1 else 0)
       else if (j = 1) then 1 else 0  (* add the last n = 1, always coprime *)
`;
*)

(* Count the number of coprimes, linear stack version *)
val count_coprime_def = Define `
    count_coprime n j =
           if j = 0 then 0
      else if j = 1 then 1
      else count_coprime n (j - 1) + (if (gcd_compute j n = 1) then 1 else 0)
`;

(* Compute phi function *)
val phi_compute_def = Define`
    phi_compute n = count_coprime n n
`;

(*
> EVAL ``phi_compute 0``; --> 0
> EVAL ``phi_compute 1``; --> 1
> EVAL ``phi_compute 2``; --> 1
> EVAL ``phi_compute 3``; --> 2
> EVAL ``phi_compute 4``; --> 2
> EVAL ``phi_compute 5``; --> 4
> EVAL ``phi_compute 6``; --> 2
> EVAL ``phi_compute 7``; --> 6
> EVAL ``phi_compute 8``; --> 4
> EVAL ``phi_compute 9``; --> 6
> EVAL ``phi_compute 10``; --> 4
*)

(* Theorem: phi_compute 0 = 0 *)
(* Proof:
     phi_compute 0
   = count_coprime 0 0    by phi_compute_def
   = 0                    by count_coprime_def
*)
val phi_compute_0 = store_thm(
  "phi_compute_0",
  ``phi_compute 0 = 0``,
  rw[phi_compute_def, Once count_coprime_def]);

(* Theorem: phi_compute 1 = 1 *)
(* Proof:
     phi_compute 1
   = count_coprime 1 1    by phi_compute_def
   = 1                    by count_coprime_def
*)
val phi_compute_1 = store_thm(
  "phi_compute_1",
  ``phi_compute 1 = 1``,
  rw[phi_compute_def, Once count_coprime_def]);

(* Theorem: count_coprime n 0 = 0 *)
(* Proof: by count_coprime_def *)
val count_coprime_0 = store_thm(
  "count_coprime_0",
  ``!n. count_coprime n 0 = 0``,
  rw[Once count_coprime_def]);

(* Theorem: count_coprime n 1 = 1 *)
(* Proof: by count_coprime_def *)
val count_coprime_1 = store_thm(
  "count_coprime_1",
  ``!n. count_coprime n 1 = 1``,
  rw[Once count_coprime_def]);

(* Theorem: count_coprime n j = if j = 0 then 0 else if j = 1 then 1 else
                                count_coprime n (j - 1) + if coprime j n then 1 else 0 *)
(* Proof: by count_coprime_def, gcd_compute_eqn *)
val count_coprime_alt = store_thm(
  "count_coprime_alt",
  ``!n j. count_coprime n j = if j = 0 then 0 else if j = 1 then 1 else
                             count_coprime n (j - 1) + if coprime j n then 1 else 0``,
  rw[Once count_coprime_def, gcd_compute_eqn]);

(* Theorem: count_coprime n (SUC k) = count_coprime n k + (if coprime (SUC k) n then 1 else 0) *)
(* Proof:
   Apply count_coprime_def, this is to show:
   (1) coprime (SUC 0) n ==> 1 = count_coprime n 0 + 1, true   by count_coprime_0
   (2) gcd (SUC 0) n <> 1 ==> 1 = count_coprime n 0, true      by GCD_1
*)
val count_coprime_suc = store_thm(
  "count_coprime_suc",
  ``!n k. count_coprime n (SUC k) = count_coprime n k + (if coprime (SUC k) n then 1 else 0)``,
  rw[Once count_coprime_alt] >-
  rw[count_coprime_0] >>
  fs[GCD_1]);

(* Theorem: k <= n ==> (count_coprime n k = CARD ((coprimes n) INTER (natural k))) *)
(* Proof:
   By induction on k.
   Base: count_coprime n 0 = CARD (coprimes n INTER natural 0)
      LHS = count_coprime n 0 = 0                   by count_coprime_0
      RHS = CARD (coprimes n INTER natural 0)
          = CARD (coprimes n INTER {})              by natural_0
          = CARD {}                                 by INTER_EMPTY
          = 0 = LHS                                 by CARD_EMPTY
   Step: count_coprime n k = CARD (coprimes n INTER natural k) ==>
         count_coprime n (SUC k) = CARD (coprimes n INTER natural (SUC k))

      If coprime (SUC k) n, then (SUC k) IN (coprimes n)           by coprimes_element
         But (SUC k) NOTIN (natural k)                             by natural_element
         Thus (SUC k) NOTIN (natural k) INTER (coprimes n)         by IN_INTER
         Note FINITE (natural k)                                   by natural_finite
          and FINITE (coprimes n)                                  by coprimes_finite
          ==> FINITE (natural k) INTER (coprimes n)                by FINITE_INTER

            CARD (coprimes n INTER natural (SUC k))
          = CARD (natural (SUC k) INTER coprimes n)                by INTER_COMM
          = CARD (((SUC k) INSERT (natural k)) INTER coprimes n)   by natural_suc
          = CARD ((SUC k) INSERT ((natural k) INTER (coprimes n))) by INSERT_INTER, (SUC k) IN (coprimes n)
          = SUC (CARD ((natural k) INTER (coprimes n)))            by CARD_INSERT, (SUC k) NOTIN intersection
          = CARD ((natural k) INTER (coprimes n)) + 1              by ADD1
          = CARD ((coprimes n) INTER (natural k)) + 1              by INTER_COMM
          = count_coprime n k + 1                                  by induction hypothesis
          = count_coprime n k + (if coprime (SUC k) n then 1 else 0)
          = count_coprime n (SUC k)                                by count_coprime_suc

       If ~(coprime (SUC k) n), then (SUC k) NOTIN (coprimes n)    by coprimes_element
            CARD (coprimes n INTER natural (SUC k))
          = CARD (natural (SUC k) INTER coprimes n)                by INTER_COMM
          = CARD (((SUC k) INSERT (natural k)) INTER coprimes n)   by natural_suc
          = CARD ((natural k) INTER (coprimes n))                  by INSERT_INTER, (SUC k) NOTIN (coprimes n)
          = CARD (natural k) INTER (coprimes n) + 0                by ADD_0
          = CARD ((coprimes n) INTER (natural k)) + 0              by INTER_COMM
          = count_coprime n k + 0                                  by induction hypothesis
          = count_coprime n k + (if coprime (SUC k) n then 1 else 0)
          = count_coprime n (SUC k)                                by count_coprime_suc

*)
val count_coprime_eqn = store_thm(
  "count_coprime_eqn",
  ``!n k. k <= n ==> (count_coprime n k = CARD ((coprimes n) INTER (natural k)))``,
  rpt strip_tac >>
  Induct_on `k` >-
  rw[count_coprime_0] >>
  rw[count_coprime_suc] >| [
    `(SUC k) IN (coprimes n)` by rw[coprimes_element] >>
    `(SUC k) NOTIN (natural k)` by rw[natural_element] >>
    `(SUC k) NOTIN (natural k) INTER (coprimes n)` by rw[] >>
    `CARD (coprimes n INTER natural (SUC k)) = CARD (natural (SUC k) INTER coprimes n)` by rw[INTER_COMM] >>
    `_ = CARD (((SUC k) INSERT (natural k)) INTER coprimes n)` by rw[natural_suc] >>
    `_ = CARD ((SUC k) INSERT ((natural k) INTER (coprimes n)))` by rw[INSERT_INTER] >>
    `_ = SUC (CARD ((natural k) INTER (coprimes n)))` by rw[CARD_INSERT, natural_finite, coprimes_finite] >>
    `_ = CARD ((natural k) INTER (coprimes n)) + 1` by rw[] >>
    rw[INTER_COMM],
    `(SUC k) NOTIN (coprimes n)` by rw[coprimes_element] >>
    `CARD (coprimes n INTER natural (SUC k)) = CARD (natural (SUC k) INTER coprimes n)` by rw[INTER_COMM] >>
    `_ = CARD (((SUC k) INSERT (natural k)) INTER coprimes n)` by rw[natural_suc] >>
    `_ = CARD ((natural k) INTER (coprimes n))` by rw[INSERT_INTER] >>
    rw[INTER_COMM]
  ]);

(* Theorem: phi_compute n = phi n *)
(* Proof:
   Note (coprimes n) INTER (natural n)        by coprimes_subset
    and n <= n                                by LESS_EQ_REFL
     phi_compute n
   = count_coprime n n                        by phi_compute_def
   = CARD ((coprimes n) INTER (natural n))    by count_coprime_eqn, n <= n.
   = CARD (coprimes n)                        by SUBSET_INTER_ABSORPTION
   = phi n                                    by phi_def
*)
val phi_compute_eqn = store_thm(
  "phi_compute_eqn",
  ``!n. phi_compute n = phi n``,
  metis_tac[phi_compute_def, phi_def,
            count_coprime_eqn, coprimes_subset, SUBSET_INTER_ABSORPTION, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
