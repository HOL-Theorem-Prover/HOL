(* ------------------------------------------------------------------------- *)
(* Order Computations                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computeOrder";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory gcdTheory logrootTheory primeTheory;

open groupInstancesTheory;
open ringInstancesTheory;
open fieldInstancesTheory;
open groupOrderTheory;

open computeBasicTheory;

(* ------------------------------------------------------------------------- *)
(* Order Computations Documentation                                          *)
(* ------------------------------------------------------------------------- *)
(* Datatype and Overloading:
   sqrt_compute  = root_compute 2
*)
(* Definitions and Theorems (# are exported):

   Order Computation:
   ordz_seek_def           |- !n m j c. ordz_seek m n c j = if c <= j then 0
                                        else if n ** j MOD m = 1 then j
                                        else ordz_seek m n c (SUC j)
   ordz_seek_alt           |- !m n c j. ordz_seek m n c j = if c <= j then 0
                                        else if n ** j MOD m = 1 then j
                                        else ordz_seek m n c (j + 1)
   ordz_seek_over          |- !m n c j. c <= j ==> (ordz_seek m n c j = 0)
   ordz_seek_1_n           |- !n c j. ordz_seek 1 n c j = 0
   ordz_seek_m_0           |- !m c j. 0 < m ==> (ordz_seek m 0 c j = 0)
   ordz_seek_m_1           |- !m c j. 1 < m /\ j < c ==> (ordz_seek m 1 c j = j)
   ordz_seek_from_0        |- !m n c. 0 < m ==> (ordz_seek m n c 0 = 0)
   ordz_seek_not_0         |- !m n c j. ordz_seek m n c j <> 0 ==> j < c
   ordz_seek_exit          |- !m n c j. 0 < m /\ j < c /\ (n ** j MOD m = 1) ==>
                                        (ordz_seek m n c j = j)
   ordz_seek_next          |- !m n c j. 0 < m /\ j < c /\ n ** j MOD m <> 1 ==>
                                        (ordz_seek m n c j = ordz_seek m n c (SUC j))
   ordz_seek_not_0_lower   |- !m n c j. 0 < m /\ ordz_seek m n c j <> 0 ==> j <= ordz_seek m n c j
   ordz_seek_when_next     |- !m n c j. (ordz_seek m n c j = SUC j) ==> j < c
   ordz_seek_when_found    |- !m n c j. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j) ==> (n ** j MOD m = 1)
   ordz_seek_found_imp_1   |- !m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
                                          (n ** (j + u) MOD m = 1)
   ordz_seek_found_imp_2   |- !m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
                                          !v. v < u ==> n ** (j + v) MOD m <> 1
   ordz_seek_found_imp     |- !m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
                                          (n ** (j + u) MOD m = 1) /\
                                          !v. v < u ==> n ** (j + v) MOD m <> 1
   ordz_seek_from_1_nonzero|- !m n c. 0 < m /\ 0 < ordz_seek m n c 1 ==> (ordz_seek m n c 1 = ordz m n)
   ordz_seek_eq_0_if       |- !m n c j. 0 < m /\ 0 < j /\ (ordz_seek m n c j = 0) ==>
                                        c <= j \/ !k. j <= k /\ k < c ==> n ** k MOD m <> 1
   ordz_seek_eq_0_if_alt   |- !m n c j. 0 < m /\ 0 < j /\ j < c /\ (ordz_seek m n c j = 0) ==>
                              !k. j <= k /\ k < c ==> n ** k MOD m <> 1
   ordz_seek_eq_0_only_if  |- !m n c j. 0 < m /\
                                           (c <= j \/ 0 < j /\ !k. j <= k /\ k < c ==> n ** k MOD m <> 1) ==>
                                           (ordz_seek m n c j = 0)
   ordz_seek_eq_order      |- !m n c. 1 < m /\ m <= c ==> (ordz_seek m n c 1 = ordz m n)
   ordz_seek_thm           |- !m n. 1 < m ==> (ordz_seek m n m 1 = ordz m n)

   ordz_compute_def        |- !m n. ordz_compute m n = if m = 0 then ordz 0 n
                                        else if m = 1 then 1 else ordz_seek m n m 1
   ordz_compute_eqn        |- !m n. ordz_compute m n = ordz m n

   Order Computation -- with optimisation:
   order_search_def      |- !n m k c. order_search m n c k =
                                           if c <= k then k
                                      else if exp_mod_compute n k m = 1 then k
                                      else order_search m n c (k + 1)
   order_compute_def     |- !m n. order_compute m n =
                                       if n = 0 then ordz m 0
                                  else if m = 0 then ordz m n
                                  else if gcd_compute m n = 1 then order_search m (n MOD m) (phi_compute m) 1
                                  else 0
   order_search_alt      |- !m n c k. order_search m n c k =
                                           if c <= k then k
                                      else if n ** k MOD m = 1 then k
                                      else order_search m n c (k + 1)
   order_compute_alt     |- !m n. order_compute m n =
                                       if n = 0 then ordz m 0
                                  else if m = 0 then ordz m n
                                  else if coprime m n then order_search m (n MOD m) (phi m) 1
                                  else 0
   order_search_id       |- !m n c. order_search m n c c = c
   order_search_over     |- !m n c k. c <= k ==> (order_search m n c k = k)
   order_search_success  |- !m n c k. k < c /\ (n ** k MOD m = 1) ==> (order_search m n c k = k)
   order_search_lower    |- !m n c k. k <= order_search m n c k
   order_search_upper    |- !m n c k. order_search m n c k <= MAX k c
   order_search_property |- !m n c k. k <= c /\ (n ** c MOD m = 1) ==> (n ** order_search m n c k MOD m = 1)
   order_search_minimal  |- !m n c k. k <= c ==> !j. k <= j /\ j < order_search m n c k ==> n ** j MOD m <> 1
   order_compute_eqn     |- !m n. order_compute m n = ordz m n

   Efficient Order Computation:
   ordz_search_def       |- !n m k c. ordz_search m n c k =
                                           if c <= k then k
                                      else if k divides c /\ (exp_mod_compute n k m = 1) then k
                                      else ordz_search m n c (k + 1)
   ordz_fast_def         |- !m n. ordz_fast m n =
                                       if n = 0 then ordz m 0
                                  else if m = 0 then ordz m n
                                  else if gcd_compute m n = 1 then ordz_search m (n MOD m) (phi_compute m) 1
                                  else 0
   ordz_search_alt       |- !m n c k. ordz_search m n c k =
                                           if c <= k then k
                                      else if k divides c /\ (n ** k MOD m = 1) then k
                                      else ordz_search m n c (k + 1)
   ordz_fast_alt         |- !m n. ordz_fast m n =
                                       if n = 0 then ordz m 0
                                  else if m = 0 then ordz m n
                                  else if coprime m n then ordz_search m (n MOD m) (phi m) 1
                                  else 0
   ordz_search_id        |- !m n c. ordz_search m n c c = c
   ordz_search_over      |- !m n c k. c <= k ==> (ordz_search m n c k = k)
   ordz_search_success   |- !m n c k. k < c /\ k divides c /\ (n ** k MOD m = 1) ==> (ordz_search m n c k = k)
   ordz_search_lower     |- !m n c k. k <= ordz_search m n c k
   ordz_search_upper     |- !m n c k. ordz_search m n c k <= MAX k c
   ordz_search_property  |- !m n c k. k <= c /\ (n ** c MOD m = 1) ==>
                                      ordz_search m n c k divides c /\ (n ** ordz_search m n c k MOD m = 1)
   ordz_search_minimal   |- !m n c k. k <= c ==>
                            !j. k <= j /\ j < ordz_search m n c k ==> ~(j divides c /\ (n ** j MOD m = 1))
   ordz_fast_eqn         |- !m n. ordz_fast m n = ordz m n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Order Computation                                                         *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:
Input: m, n, c, j.  m = modulus, c = cutoff, j = initial value.
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

   if m = 0, return 0     // since (mod 0) is undefined
   loop:
      if j = m, return 0  // exit
      if (n ** j) mod m = 1 return j     // found j satisfying the condition
      j <- j + 1          // increment j
      goto loop           // go back

To compute the correct ordz m n, set initial j = 1.
The cutoff c can be (phi m),
and (phi m < m for 1 < m), or (phi m <= m for all m) by phi_le.

This is the simpliest method to arrive at a least value for order.
Other versions can optimise:
* by including coprime tests, as only n coprime with m has nonzero order.
* by including divisibility tests, as (ordz m n) must divide (phi m).

This simple method is easy for complexity analysis.

Note: ZN_order_mod_1  |- !n. ordz 1 n = 1
Thus when m = 0, should return 1.
However, this will make complexity analysis harder,
and the criteria for ordz_seek m n c j = 1 later.
Since there is a caller to ordz_seek,
better have the caller to handle this discrepancy.
This is given explicitly in ordz_seek_thm.
*)

(* Define the order seek loop *)
(*
val ordz_seek_def = tDefine "ordz_seek" `
  ordz_seek m n c j =
  if (m = 0) \/ c <= j then 0
  else if (n ** j) MOD m = 1 then j else ordz_seek m n c (SUC j)
`(WF_REL_TAC `measure (\(m,n,c,j). c - j)`);
*)
(* Use of c <= j to simplify the checks for a total function. *)
Definition ordz_seek_def:
  ordz_seek m n c j =
  if c <= j then 0
  else if (n ** j) MOD m = 1 then j else ordz_seek m n c (SUC j)
Termination
  WF_REL_TAC `measure (λ(m,n,c,j). c - j)`
End
(* Skip m = 0 as this is not critical to termination, and caller will pass m <> 0. *)

(*
setting cutoff c = m.
EVAL ``ordz_seek 7 2 7 1``; = 3 <- ordz 7 2 = 3.
EVAL ``ordz_seek 7 2 7 2``; = 3 <- j < result
EVAL ``ordz_seek 7 2 7 3``; = 3 <- j = result.
EVAL ``ordz_seek 7 2 7 4``; = 6 <- j too high, get multiple of 3.
EVAL ``ordz_seek 7 2 7 5``; = 6 <- j too high, get multiple of 3.
EVAL ``ordz_seek 7 2 7 6``; = 6 <- j too high, get multiple of 3.
EVAL ``ordz_seek 7 2 7 7``; = 0 <- j = c.
EVAL ``ordz_seek 7 10 7 1``; = 6 <- ordz 7 10 = 6.
EVAL ``ordz_seek 7 10 6 1``; = 0 <- cutoff c too low,
Need m <= c.
The MOD tests are: j = 1, 2, ..., (c - 1), since j = c will exit without MOD test.
When c = m, all j = 1 to (m - 1) are tested. If no MOD equal to 1, return 0.
*)

(* Theorem: ordz_seek m n c j = if c <= j then 0
            else if (n ** j) MOD m = 1 then j else ordz_seek m n c (j + 1) *)
(* Proof: by ordz_seek_def *)
val ordz_seek_alt = store_thm(
  "ordz_seek_alt",
  ``!m n c j. ordz_seek m n c j = if c <= j then 0
             else if (n ** j) MOD m = 1 then j else ordz_seek m n c (j + 1)``,
  rw[Once ordz_seek_def, ADD1]);

(* Theorem: c <= j ==> (ordz_seek m n c j = 0) *)
(* Proof: by ordz_seek_def. *)
val ordz_seek_over = store_thm(
  "ordz_seek_over",
  ``!m n c j. c <= j ==> (ordz_seek m n c j = 0)``,
  rw[Once ordz_seek_def]);

(* Theorem: ordz_seek 1 n c j = 0 *)
(* Proof:
   By induction on (c - j).
   Base: !c j. (0 = c - j) ==> (ordz_seek 1 n c j = 0)
             0 = c - j
         ==> c <= j                     by integer arithmetic
         ==> ordz_seek 1 n c j = 0      by ordz_seek_def
   Step: !c j. (v = c - j) ==> (ordz_seek 1 n c j = 0) ==>
         !c j. (SUC v = c - j) ==> (ordz_seek 1 n c j = 0)
         SUC v = c - j means v = c - j - 1 = c - SUC j.
         and 0 < c - j means ~(c <= j).
         But n ** j MOD 1 = 0                by MOD_1
         Thus ordz_seek 1 n c j
            = ordz_seek 1 n c (SUC j)        by ordz_seek_def, n ** j MOD 1 <> 1
            = 0                              by induction hypothesis
*)
val ordz_seek_1_n = store_thm(
  "ordz_seek_1_n",
  ``!n c j. ordz_seek 1 n c j = 0``,
  rpt strip_tac >>
  Induct_on `c - j` >-
  rw[Once ordz_seek_def] >>
  rw[Once ordz_seek_def]);

(* Theorem: 0 < m ==> (ordz_seek m 0 c j = 0) *)
(* Proof:
   By induction on (c - j).
   Base: !c j. (0 = c - j) ==> (ordz_seek m 0 c j = 0)
             0 = c - j
         ==> c <= j                     by integer arithmetic
         ==> ordz_seek 1 n c j = 0      by ordz_seek_def
   Step: !c j. (v = c - j) ==> (ordz_seek m 0 c j = 0) ==>
         !c j. (SUC v = c - j) ==> (ordz_seek m 0 c j = 0)
         SUC v = c - j means v = c - j - 1 = c - SUC j.
         and 0 < c - j means ~(c <= j).
         If m = 0, ordz_seek m 0 c j = 0     by ordz_seek_def
         If m <> 0,
            Note 0 ** j MOD m = 0            by ZERO_MOD, 0 < m
            ordz_seek m 0 c j
          = ordz_seek m 0 c (SUC j)          by ordz_seek_def, n ** j MOD m <> 1
          = 0                                by induction hypothesis
*)
val ordz_seek_m_0 = store_thm(
  "ordz_seek_m_0",
  ``!m c j. 0 < m ==> (ordz_seek m 0 c j = 0)``,
  rpt strip_tac >>
  Induct_on `c - j` >-
  rw[Once ordz_seek_def] >>
  rw[Once ordz_seek_def] >>
  metis_tac[ZERO_EXP, ZERO_MOD, ONE_NOT_ZERO]);

(* Theorem: 1 < m /\ j < c ==> (ordz_seek m 1 c j = j) *)
(* Proof:
   Note j < c means ~(c <= j)             by arithmetic
    and 1 ** j MOD m
      = 1 MOD m                           by EXP_1
      = 1                                 by ONE_MOD, 1 < m
   Thus ordz_seek m 1 c j = SUC (c - j)   by ordz_seek_def
*)
val ordz_seek_m_1 = store_thm(
  "ordz_seek_m_1",
  ``!m c j. 1 < m /\ j < c ==> (ordz_seek m 1 c j = j)``,
  rw[Once ordz_seek_def]);

(* Theorem: 0 < m ==> (ordz_seek m n c 0 = 0) *)
(* Proof:
   If m = 1, ordz_seek m n c 0 = 0       by ordz_seek_1_n
   Otherwise, 1 < m.
     ordz_seek m n c 0
   = if c <= 0 then 0
     else if n ** 0 MOD m = 1 then 0
     else ordz_seek m n c 1              by ordz_seek_def
   Note n ** 0 MOD m
      = 1 MOD m                          by EXP_0
      = 1                                by ONE_MOD, 1 < m
   Thus ordz_seek m n c 0 = 0.
*)
val ordz_seek_from_0 = store_thm(
  "ordz_seek_from_0",
  ``!m n c. 0 < m ==> (ordz_seek m n c 0 = 0)``,
  rpt strip_tac >>
  (Cases_on `m = 1` >> simp[ordz_seek_1_n]) >>
  `n ** 0 MOD m = 1` by rw[EXP_0, ONE_MOD] >>
  rw[Once ordz_seek_def]);

(* Theorem: ordz_seek m n c j <> 0 ==> j < c *)
(* Proof: by ordz_seek_def *)
val ordz_seek_not_0 = store_thm(
  "ordz_seek_not_0",
  ``!m n c j. ordz_seek m n c j <> 0 ==> j < c``,
  rw[Once ordz_seek_def]);

(* Theorem: 0 < m /\ j < c /\ (n ** j MOD m = 1) ==> (ordz_seek m n c j = j) *)
(* Proof: by ordz_seek_def *)
val ordz_seek_exit = store_thm(
  "ordz_seek_exit",
  ``!m n c j. 0 < m /\ j < c /\ (n ** j MOD m = 1) ==> (ordz_seek m n c j = j)``,
  rw[Once ordz_seek_def]);

(* Theorem: 0 < m /\ j < c /\
            (n ** j MOD m <> 1) ==> (ordz_seek m n c j = ordz_seek m n c (SUC j)) *)
(* Proof: by ordz_seek_def *)
val ordz_seek_next = store_thm(
  "ordz_seek_next",
  ``!m n c j. 0 < m /\ j < c /\
             (n ** j MOD m <> 1) ==> (ordz_seek m n c j = ordz_seek m n c (SUC j))``,
  rw[Once ordz_seek_def]);

(* Theorem: 0 < m /\ ordz_seek m n c j <> 0 ==> j <= ordz_seek m n c j *)
(* Proof:
   By induction on ordz_seek_def, to show:
      ordz_seek m n c j <> 0 ==> j <= ordz_seek m n c j
   Note ordz_seek m n c j <> 0              by given
    ==> 0 < j                               by ordz_seek_not_0
   If n ** j MOD m = 1,
      Then ordz_seek m n c j = j            by ordz_seek_exit, 0 < m
   If n ** j MOD m <> 1,
      Then ordz_seek m n c j
         = ordz_seek m n c (SUC j)          by ordz_seek_next
         >= SUC j                           by induction hypothesis
         >= j                               by arithmetic
*)
val ordz_seek_not_0_lower = store_thm(
  "ordz_seek_not_0_lower",
  ``!m n c j. 0 < m /\ ordz_seek m n c j <> 0 ==> j <= ordz_seek m n c j``,
  ho_match_mp_tac (theorem "ordz_seek_ind") >>
  rw[] >>
  imp_res_tac ordz_seek_not_0 >>
  Cases_on `n ** j MOD m = 1` >-
  rw[ordz_seek_exit] >>
  `ordz_seek m n c j = ordz_seek m n c (SUC j)` by rw[GSYM ordz_seek_next] >>
  decide_tac);

(* Theorem: (ordz_seek m n c j = SUC j) ==> j < c *)
(* Proof:
   Note ordz_seek m n c j <> 0          by 0 < SUC j
    ==> j < c                           by ordz_seek_not_0
*)
val ordz_seek_when_next = store_thm(
  "ordz_seek_when_next",
  ``!m n c j. (ordz_seek m n c j = SUC j) ==> j < c``,
  rpt strip_tac >>
  `ordz_seek m n c j <> 0` by fs[] >>
  imp_res_tac ordz_seek_not_0);

(* Theorem: 0 < m /\ 0 < j /\ (ordz_seek m n c j = j) ==> (n ** j MOD m = 1) *)
(* Proof:
   By contradiction, suppose n ** j MOD m <> 1.
   Note ordz_seek m n c j <> 0                         by ordz_seek m n c j = j, 0 < j
   Thus 0 < j                                          by ordz_seek_not_0
    ==> ordz_seek m n c j = ordz_seek m n c (SUC j)    by ordz_seek_next, n ** j MOD m <> 1
    But SUC j <= ordz_seek m n c (SUC j)               by ordz_seek_not_0_lower
    ==> SUC j <= j                                     by ordz_seek m n c j = j
    This contradicts j < SUC j                         by LESS_SUC
*)
val ordz_seek_when_found = store_thm(
  "ordz_seek_when_found",
  ``!m n c j. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j) ==> (n ** j MOD m = 1)``,
  spose_not_then strip_assume_tac >>
  `ordz_seek m n c j <> 0` by fs[] >>
  imp_res_tac ordz_seek_not_0 >>
  `ordz_seek m n c j = ordz_seek m n c (SUC j)` by rw[GSYM ordz_seek_next] >>
  `SUC j <= ordz_seek m n c (SUC j)` by rw[ordz_seek_not_0_lower] >>
  decide_tac);

(* This is a special case of the next theorem when u = 0. *)

(* Theorem: 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
            (n ** (j + u) MOD m = 1) *)
(* Proof:
   By induction from ordz_seek_def, to show:
      0 < j /\ ordz_seek m n c j = j + u ==> n ** (j + u) MOD m = 1
   Note ordz_seek m n c j <> 0              by 0 < j
    ==> j < c                               by ordz_seek_not_0
   If n ** j MOD m = 1,
      Then ordz_seek m n c j = j            by ordz_seek_exit
       ==>             j + u = j            by ordz_seek m n c j = j + u
        or                 u = 0            by arithmetic
           n ** (j + u) MOD m
         = n ** j MOD m                     by ADD_0
         = 1                                by this case.
   If n ** j MOD m <> 1,
      Then ordz_seek m n c j
         = ordz_seek m n c (SUC j)          by ordz_seek_next
      Note u <> 1                           by ordz_seek_when_found, ADD_0
      Let v = u - 1.
      Then v + SUC j = j + u                by arithmetic
           n ** (j + u) MOD m
         = n ** (v + SUC j) MOD m           by above
         = 1                                by induction hypothesis
*)
val ordz_seek_found_imp_1 = store_thm(
  "ordz_seek_found_imp_1",
  ``!m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==> (n ** (j + u) MOD m = 1)``,
  ho_match_mp_tac (theorem "ordz_seek_ind") >>
  rw[] >>
  `ordz_seek m n c j <> 0` by decide_tac >>
  imp_res_tac ordz_seek_not_0 >>
  Cases_on `n ** j MOD m = 1` >| [
    `ordz_seek m n c j = j` by rw[GSYM ordz_seek_exit] >>
    `u = 0` by decide_tac >>
    simp[],
    `ordz_seek m n c j = ordz_seek m n c (SUC j)` by rw[GSYM ordz_seek_next] >>
    `u <> 0` by metis_tac[ordz_seek_when_found, ADD_0] >>
    qabbrev_tac `v = u - 1` >>
    `v + SUC j = j + u` by rw[Abbr`v`] >>
    metis_tac[NOT_ZERO, NOT_LESS]
  ]);

(* Theorem: 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
           !v. v < u ==> n ** (j + v) MOD m <> 1 *)
(* Proof:
   By induction from ordz_seek_def, to show:
      0 < j /\ ordz_seek m n c j = j + u /\ v < u ==> n ** (j + v) MOD m <> 1
   By contradiction, suppose n ** (j + v) MOD m = 1.
   Note ordz_seek m n c j <> 0              by ordz_seek m n c j = j + u, 0 < j
    ==> j < c                               by ordz_seek_not_0
   Note u <> 0                              by v < u

   If n ** j MOD m = 1,
      Then ordz_seek m n c j = j            by ordz_seek_exit
        or             j + u = j            by ordz_seek m n c j = j + u
        or u = 0, contradicts u <> 0        by ADD_0

   If n ** j MOD m <> 1,
      Then ordz_seek m n c j
         = ordz_seek m n c (SUC j)          by ordz_seek_next
      Note v <> 0                           by n ** (j + v) MOD m = 1, ADD_0
      Let k = u - 1, h = v - 1.
      Then h < k /\ SUC j + k = j + u /\ SUC j + h = j + v
                                            by arithmetic
       ==> n ** (j + v) MOD m <> 1          by induction hypothesis
      This contradicts n ** (j + v) MOD m = 1.
*)
val ordz_seek_found_imp_2 = store_thm(
  "ordz_seek_found_imp_2",
  ``!m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
         !v. v < u ==> n ** (j + v) MOD m <> 1``,
  ho_match_mp_tac (theorem "ordz_seek_ind") >>
  spose_not_then strip_assume_tac >>
  `ordz_seek m n c j <> 0` by decide_tac >>
  imp_res_tac ordz_seek_not_0 >>
  `u <> 0` by decide_tac >>
  Cases_on `n ** j MOD m = 1` >| [
    `ordz_seek m n c j = j` by rw[GSYM ordz_seek_exit] >>
    decide_tac,
    `ordz_seek m n c j = ordz_seek m n c (SUC j)` by rw[GSYM ordz_seek_next] >>
    `v <> 0` by metis_tac[ADD_0] >>
    qabbrev_tac `k = u - 1` >>
    qabbrev_tac `h = v - 1` >>
    `j + u = SUC j + k` by rw[Abbr`k`] >>
    `j + v = SUC j + h` by rw[Abbr`h`] >>
    `h < k` by rw[Abbr`h`, Abbr`k`] >>
    `0 < SUC j` by decide_tac >>
    metis_tac[NOT_ZERO, NOT_LESS]
  ]);

(* Combine to form a major result *)

(* Theorem: 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
            ((n ** (j + u) MOD m = 1) /\ !v. v < u ==> n ** (j + v) MOD m <> 1) *)
(* Proof: by ordz_seek_found_imp_1, ordz_seek_found_imp_2 *)
val ordz_seek_found_imp = store_thm(
  "ordz_seek_found_imp",
  ``!m n c j u. 0 < m /\ 0 < j /\ (ordz_seek m n c j = j + u) ==>
             ((n ** (j + u) MOD m = 1) /\ !v. v < u ==> n ** (j + v) MOD m <> 1)``,
  metis_tac[ordz_seek_found_imp_1, ordz_seek_found_imp_2]);

(* Theorem: 0 < m /\ 0 < ordz_seek m n c 1 ==> (ordz_seek m n c 1 = ordz m n) *)
(* Proof:
   Let k = ordz_seek m n c 1.
   Then k <> 0, so ?u. k = 1 + u                  by num_CASES
   Thus n ** k MOD m = 1 /\
        !v. v < u ==> n ** (1 + v) MOD m <> 1     by ordz_seek_found_imp, putting j = 1.
   This is the same as:
        !j. 0 < j /\ j < k ==> n ** j MOD m <> 1  by index shifting
   Also 1 < m                                     by ordz_seek_1_n, k <> 0
   Thus k = ordz m n                              by ZN_order_test_1
*)
val ordz_seek_from_1_nonzero = store_thm(
  "ordz_seek_from_1_nonzero",
  ``!m n c. 0 < m /\ 0 < ordz_seek m n c 1 ==> (ordz_seek m n c 1 = ordz m n)``,
  rpt strip_tac >>
  qabbrev_tac `k = ordz_seek m n c 1` >>
  `k <> 0 /\ 0 < 1` by decide_tac >>
  `?u. k = 1 + u` by metis_tac[num_CASES, SUC_ONE_ADD] >>
  `(n ** k MOD m = 1) /\ !v. v < u ==> n ** (1 + v) MOD m <> 1` by metis_tac[ordz_seek_found_imp] >>
  `!j. 0 < j /\ j < k ==> n ** j MOD m <> 1` by
  (rpt strip_tac >>
  `?v. j = 1 + v` by metis_tac[num_CASES, SUC_ONE_ADD, NOT_ZERO] >>
  `v < u` by decide_tac >>
  metis_tac[]) >>
  `m <> 1` by metis_tac[ordz_seek_1_n] >>
  rw[ZN_order_test_1]);

(* Theorem: 0 < m /\ 0 < j /\ (ordz_seek m n c j = 0) ==>
            (c <= j \/ (!k. j <= k /\ k < c ==> (n ** k) MOD m <> 1)) *)
(* Proof:
   Idea:
   The induction is based on the range [j ..< c].
   Note ordz_seek m n c j = 0    by given
        ordz_seek m n c c = 0    by definition
   By contradiction, there is a k in the range [j ..< c]
   such that   (n ** k) MOD m = 1.

   If SUC j = c, the smallest range,
      Then k = j, as k is now squeezed between [j ..< SUC j].
      Then k < c                       by j < c
       and (n ** k) MOD m = 1          by contradiction
       ==> ordz_seek m n c k = k       by ordz_seek_exit
        or ordz_seek m n c j = j       by k = j
      This contradicts
           ordz_seek m n c j = 0       by 0 < j

   Otherwise, SUC j < c                by j < c means SUC j <= c, noew SUC j <> c.
      Then !k. SUC j <= k /\ k < c ==> n ** k MOD m <> 1
                                       by induction hypothesis
      Note j <= k means j = k \/ j < k by k in [j ..< c]
      If j = k, we have the same contradiction as before:
         Since (n ** k) MOD m = 1
         gives (n ** j) MOD m = 1
          thus ordz_seek m n c j = j   by ordz_seek_exit
         This contradicts
           ordz_seek m n c j = 0       by 0 < j
      If j < k, this is the same as SUC j <= k.
         Thus the induction implication applies,
         giving n ** k MOD m <> 1
         This contradicts n ** k MOD m = 1.

   By induction from ordz_seek_def, to show:
       j < c /\ n ** j MOD m <> 1 ==>
       (ordz_seek m n c (SUC j) = 0) ==>
       c <= SUC j \/ !k. SUC j <= k /\ k < c ==> n ** k MOD m <> 1
   Note 0 < j /\ j < c /\ ordz_seek m n c j = 0
    ==> n ** j MOD m <> 1               by ordz_seek_exit

   By contradiction, suppose the opposite:
       ordz_seek m n c (SUC j) = 0 /\ SUC j < c /\
       ?k. SUC j <= k /\ k < c ==> n ** k MOD m <> 1
   Thus k <> j, as n ** k MOD m = 1     by contradiction
   Note j < c means SUC j <= c.
    But SUC j <> c, as that will squeeze k = j, which contradicts k <> j.
   Thus SUC j < c.
   Also j <= k /\ k <> j means j < k, tus SUC j <= k.
   With k < c, this leads to n ** k MOD <> 1, a contradiction.
*)
val ordz_seek_eq_0_if = store_thm(
  "ordz_seek_eq_0_if",
  ``!m n c j. 0 < m /\ 0 < j /\ (ordz_seek m n c j = 0) ==>
             (c <= j \/ (!k. j <= k /\ k < c ==> (n ** k) MOD m <> 1))``,
  ho_match_mp_tac (theorem "ordz_seek_ind") >>
  spose_not_then strip_assume_tac >>
  `j < c /\ j <> 0 /\ 0 < SUC j` by decide_tac >>
  `n ** j MOD m <> 1` by metis_tac[ordz_seek_exit] >>
  `ordz_seek m n c (SUC j) = 0` by rw[GSYM ordz_seek_next] >>
  `k <> j` by metis_tac[] >>
  first_x_assum (drule_all_then strip_assume_tac) >-
  decide_tac >>
  `SUC j <= k` by decide_tac >>
  metis_tac[]);

(* An alternative expression of the same theorem. *)

(* Theorem: 0 < m /\ 0 < j /\ j < c /\ (ordz_seek m n c j = 0) ==>
             !k. j <= k /\ k < c ==> (n ** k) MOD m <> 1 *)
(* Proof: by ordz_seek_eq_0_if. *)
val ordz_seek_eq_0_if_alt = store_thm(
  "ordz_seek_eq_0_if_alt",
  ``!m n c j. 0 < m /\ 0 < j /\ j < c /\ (ordz_seek m n c j = 0) ==>
             !k. j <= k /\ k < c ==> (n ** k) MOD m <> 1``,
  metis_tac[ordz_seek_eq_0_if, NOT_LESS]);

(* Theorem: 0 < m /\
            (c <= j \/ (0 < j /\ !k. j <= k /\ k < c ==> (n ** k) MOD m <> 1)) ==>
            (ordz_seek m n c j = 0) *)
(* Proof:
   By induction from ordz_seek_def, to show:
   (1) c <= j ==> ordz_seek m n c j = 0, true    by ordz_seek_def, c <= j
   (2) 0 < j /\ !k. j <= k /\ k < c ==> n ** k MOD m <> 1 ==> ordz_seek m n c j = 0
       By contradiction, suppose ordz_seek m n c j <> 0.
       Then m <> 0 /\ j <> 0                     by ordz_seek_not_0
       If n ** j MOD m = 1,
          Note j <= j                            by arithmetic
           ==> n ** j MOD m <> 1                 by !k implication
          This contradicts n ** j MOD m = 1      by this case.
       If n ** j MOD m <> 1,
          Then ordz_seek m n c j
             = ordz_seek m n c (SUC j)           by ordz_seek_next
           But j < c means SUC j <= c, or ~(c < SUC j)
           ==> ordz_seek m n c (SUC j) = 0       by induction hypothesis
          This contradicts ordz_seek m n c j <> 0.
*)
val ordz_seek_eq_0_only_if = store_thm(
  "ordz_seek_eq_0_only_if",
  ``!m n c j. 0 < m /\
             (c <= j \/ (0 < j /\ !k. j <= k /\ k < c ==> (n ** k) MOD m <> 1)) ==>
             (ordz_seek m n c j = 0)``,
  ho_match_mp_tac (theorem "ordz_seek_ind") >>
  spose_not_then strip_assume_tac >-
  fs[Once ordz_seek_def] >>
  imp_res_tac ordz_seek_not_0 >>
  Cases_on `n ** j MOD m = 1` >-
  metis_tac[LESS_EQ_REFL] >>
  `ordz_seek m n c j = ordz_seek m n c (SUC j)` by rw[ordz_seek_next] >>
  `~(c <= SUC j)` by decide_tac >>
  `ordz_seek m n c (SUC j) = 0` by fs[] >>
  decide_tac);

(* Theorem: 1 < m /\ m <= c ==> (ordz_seek m n c 1 = ordz m n) *)
(* Proof:
   If ordz_seek m n c 1 = 0,
      Note 0 < 1 /\ 1 < c                 by 1 < m, m <= c
      Then !k. 0 < k /\ k < c ==> n ** k MOD m <> 1
                                          by ordz_seek_eq_0_if_alt, put j = 1
      Thus ordz m n = 0                   by ZN_order_eq_0_test, 1 < m
   If ordz_seek m n c 1 <> 0,
      Then ordz_seek m n c 1 = ordz m n   by ordz_seek_from_1_nonzero
*)
val ordz_seek_eq_order = store_thm(
  "ordz_seek_eq_order",
  ``!m n c. 1 < m /\ m <= c ==> (ordz_seek m n c 1 = ordz m n)``,
  rpt strip_tac >>
  Cases_on `ordz_seek m n c 1 = 0` >| [
    `0 < m /\ 0 < 1 /\ 1 < c` by decide_tac >>
    `!k. 1 <= k <=> 0 < k` by decide_tac >>
    `!k. 0 < k /\ k < c ==> n ** k MOD m <> 1` by metis_tac[ordz_seek_eq_0_if_alt] >>
    rw[ZN_order_eq_0_test],
    rw[ordz_seek_from_1_nonzero]
  ]);

(* Theorem: 1 < m ==> (ordz_seek m n m 1 = ordz m n) *)
(* Proof: by ordz_seek_eq_order, c = m <= m. *)
val ordz_seek_thm = store_thm(
  "ordz_seek_thm",
  ``!m n. 1 < m ==> (ordz_seek m n m 1 = ordz m n)``,
  rw[ordz_seek_eq_order]);

(* Compute ordz m n, the simplest way *)
val ordz_compute_def = Define`
    ordz_compute m n =
         if m = 0 then ordz 0 n  (* MOD 0 is undefined *)
    else if m = 1 then 1         (* ordz 1 n = 1 by ZN_order_mod_1 *)
    else ordz_seek m n m 1
         (* just the least k from 1 such that n ** k MOD m = 1 when 1 < m *)
         (* if n = 0, ordz m 0 = 0 by ZN_order_0, and ordz_seek m 0 c j = 0 by ordz_seek_m_0 *)
`;

(* Examples:
> EVAL ``ordz_compute 2 10``; = 0     1/2 = 0.5 terminating.
> EVAL ``ordz_compute 3 10``; = 1     1/3 = 0.3333  with period 1.
> EVAL ``ordz_compute 4 10``; = 0     1/4 = 0.25 terminating
> EVAL ``ordz_compute 5 10``; = 0     1/5 = 0.2  terminating
> EVAL ``ordz_compute 6 10``; = 0     1/6 = 0.16666 ...  mixed, gcd (6, 10) = 2.
> EVAL ``ordz_compute 7 10``; = 6     1/7 = 0.142857.... with period 6.
> EVAL ``ordz_compute 8 10``; = 0     1/8 = 0.125 terminating
> EVAL ``ordz_compute 9 10``; = 1     1/9 = 0.1111 ... with period 1.
> EVAL ``ordz_compute 10 10``; = 0    1/10 = 0.1  terminating
> EVAL ``ordz_compute 11 10``; = 2    1/11 = 0.0909 ... with period 2.
> EVAL ``ordz_compute 12 10``; = 0    1/12 = 0.0833 ... mixed, gcd (12,10) = 2
> EVAL ``ordz_compute 13 10``; = 6    1/13 = 0.076923076923 ... with period 6.
> EVAL ``ordz_compute 17 10``; = 16   1/17 = 0.0588235294117647 ... with period 16.
*)

(* Theorem: ordz_compute m n = ordz m n *)
(* Proof:
   If m = 0, both are equal        by ordz_compute_def
   If m = 1,
      LHS = ordz_compute 1 n = 1   by ordz_compute_def
      RHS = ordz 1 n = 1           by ZN_order_mod_1
      hence they are equal.
   Otherwise, 1 < m.
        ordz_compute m n
      = ordz_seek m n m 1          by ordz_compute_def
      = ordz m n                   by ordz_seek_eq_order, 1 < m
*)
val ordz_compute_eqn = store_thm(
  "ordz_compute_eqn",
  ``!m n. ordz_compute m n = ordz m n``,
  rw[ordz_compute_def, ZN_order_mod_1, ordz_seek_eq_order]);

(* ------------------------------------------------------------------------- *)
(* Order Computation -- with optimisation                                    *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: m, n with 1 < m, 0 < n
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

if ~(coprime m n) return 0    // initial check
// For coprime m n, ordz m (n MOD m) is a divisor of (phi m) by Euler-Fermat Theorem.
// Search upwards for least index j
j <- 1                        // initial index
c <- phi m                    // recompute constant
n <- n MOD m                  // reduce n, by ordz m n = ordz m (n MOD m)
while (j <= c) {
   if (n ** j = 1 (mod m)) return j  // test j
   j <- j + 1                        // increment j
}
return 0  // unreachable, unless no initial coprime check.

*)

(* A method to compute ordz m n:
Step 1: if (gcd m n <> 1) then 0
Step 2: Just search from j = 1 to (phi m),
        If exp_mod_compute n j m = 1, return j.
        Search is upwards for the first (least) index j.
*)

(* Question: How to show the number of steps is bounded? *)

(* Formulate a recursive search for the least index, not using WHILE loop. *)
Definition order_search_def:
  order_search m n c k =
  (* search is from k to maximum c *)
  if c <= k then k (* when k reaches c, k = c, must divide c, and exp_mod_compute n c m = 1 always. *)
  else if exp_mod_compute n k m = 1 then k (* that is, found k such that (n ** k) MOD m = 1 *)
  else order_search m n c (k + 1) (* current k is not suitable, try k + 1 instead. *)
Termination WF_REL_TAC `measure (λ(m,n,c,k). c - k)`
End
(*
val order_search_def = |- !n m k c. order_search m n c k =
     if c <= k then k
     else if exp_mod_compute n k m = 1 then k
     else order_search m n c (k + 1): thm
*)

(* Compute ordz m n *)
val order_compute_def = Define`
    order_compute m n =
         if n = 0 then ordz m 0   (* order is defined for nonzero only *)
    else if m = 0 then ordz m n  (* MOD 0 is undefined *)
    else if (gcd_compute m n = 1) (* For coprimes, search from 1 ... *)
         then order_search m (n MOD m) (phi_compute m) 1 (* ordz m n = ordz m (n MOD m), divisor of phi m *)
         else 0 (* not coprime: order is 0 *)
`;

(* Examples:
> EVAL ``order_compute 10 3``; --> 4
> EVAL ``order_compute 10 4``; --> 0
> EVAL ``order_compute 10 7``; --> 4
> EVAL ``order_compute 10 19``; --> 2
> EVAL ``order_compute 10 1``; --> 1

> EVAL ``phi_compute 10``; --> 4

Indeed, (ordz m n) is a divisor of (phi m).
Since phi(10) = 4, ordz 10 n is a divisior of 4.

> EVAL ``order_compute 1 2``; --> 1
> EVAL ``order_compute 1 3``; --> 1

*)

(* Theorem: order_search m n c k = if c <= k then k
            else if (n ** k) MOD m = 1 then k else order_search m n c (k + 1) *)
(* Proof: by order_search_def, exp_mod_compute_eqn *)
val order_search_alt = store_thm(
  "order_search_alt",
  ``!m n c k. order_search m n c k = if c <= k then k
             else if (n ** k) MOD m = 1 then k else order_search m n c (k + 1)``,
  rw[Once order_search_def, exp_mod_compute_eqn]);

(* Theorem: order_compute m n = if n = 0 then ordz m 0
                                else if m = 0 then ordz m n
                                else if coprime m n then order_search m (n MOD m) (phi m) 1 else 0 *)
(* Proof: by order_compute_def, gcd_compute_eqn, phi_compute_eqn *)
val order_compute_alt = store_thm(
  "order_compute_alt",
  ``!m n. order_compute m n =
     if n = 0 then ordz m 0
     else if m = 0 then ordz m n
     else if coprime m n then order_search m (n MOD m) (phi m) 1 else 0``,
  rw[order_compute_def, gcd_compute_eqn, phi_compute_eqn]);

(* Theorem: order_search m n c c = c *)
(* Proof: order_search_def *)
val order_search_id = store_thm(
  "order_search_id",
  ``!m n c. order_search m n c c = c``,
  rw[Once order_search_def]);

(* Theorem: c <= k ==> (order_search m n c k = k) *)
(* Proof: order_search_def *)
val order_search_over = store_thm(
  "order_search_over",
  ``!m n c k. c <= k ==> (order_search m n c k = k)``,
  rw[Once order_search_def]);

(* Theorem: k < c /\ ((n ** k) MOD m = 1) ==> (order_search m n c k = k) *)
(* Proof: by order_search_alt *)
val order_search_success = store_thm(
  "order_search_success",
  ``!m n c k. k < c /\ ((n ** k) MOD m = 1) ==> (order_search m n c k = k)``,
  rw[Once order_search_alt]);

(* Theorem: k <= order_search m n c k *)
(* Proof:
   By induction on (c - k).
   Base: (0 = c - k) ==> k <= order_search m n c k
      Note 0 = c - k means c <= k,
        or c <= k                      by SUB_EQ_0
           order_search m n c k
         = k                           by order_search_alt, ~(k < c)
         >= k                          by LESS_OR_EQ
   Step: !c k. (v = c - k) ==> k <= order_search m n c k ==>
         (SUC v = c - k) ==> k <= order_search m n c k
      Note SUC v = c - k means k < c   by SUC_POS
        or v + 1 = c - k, or
               v = c - (k + 1)         by arithmetic
        If n ** k MOD m = 1,
           order_search m n c k
         = k                           by order_search_alt, k < c
         >= k                          by LESS_OR_EQ
        If n ** k MOD m <> 1,
           order_search m n c k
         = order_search m n c (k + 1)  by order_search_alt, k < c
         >= k + 1                      by induction hypothesis
         >= k                          by arithmetic
*)
val order_search_lower = store_thm(
  "order_search_lower",
  ``!m n c k. k <= order_search m n c k``,
  rpt strip_tac >>
  Induct_on `c - k` >| [
    rpt strip_tac >>
    rw[Once order_search_alt],
    rpt strip_tac >>
    `v = c - (k + 1)` by decide_tac >>
    rw[Once order_search_alt] >>
    metis_tac[LESS_EQ_TRANS, DECIDE``k <= k + 1``]
  ]);

(* Theorem: order_search m n c k <= MAX k c *)
(* Proof:
   By induction on (c - k).
   Base: (0 = c - k) ==> order_search m n c k <= MAX k c
      Note 0 = c - k means c <= k,
        or c <= k                      by SUB_EQ_0
           order_search m n c k
         = k                           by order_search_alt, ~(k < c)
         = MAX k c                     by c <= k
         <= MAX k c                    by LESS_OR_EQ
   Step: !c k. (v = c - k) ==> order_search m n c k <= MAX k c ==>
         (SUC v = c - k) ==> order_search m n c k <= MAX k c
      Note SUC v = c - k means k < c   by SUC_POS
        or v + 1 = c - k, or
               v = c - (k + 1)         by arithmetic
        If n ** k MOD m = 1,
           order_search m n c k
         = k                           by order_search_alt, k < c
         <= c                          by LESS_OR_EQ
        If n ** k MOD m <> 1,
           order_search m n c k
         = order_search m n c (k + 1)  by order_search_alt, k < c
         <= MAX (k + 1) c              by induction hypothesis
         <= MAX k c                    by k < c ==> (k + 1) <= c
        Indeed, MAX (k + 1) c = c = MAX k c   by MAX_DEF
*)
val order_search_upper = store_thm(
  "order_search_upper",
  ``!m n c k. order_search m n c k <= MAX k c``,
  rpt strip_tac >>
  Induct_on `c - k` >| [
    rpt strip_tac >>
    rw[Once order_search_alt],
    rpt strip_tac >>
    `v = c - (k + 1)` by decide_tac >>
    `k <= MAX k c` by rw[] >>
    rw_tac bool_ss[Once order_search_alt] >>
    `MAX (k + 1) c = MAX k c` by rw[MAX_DEF] >>
    metis_tac[]
  ]);

(* Theorem: k <= c /\ ((n ** c) MOD m = 1) ==> (n ** (order_search m n c k) MOD m = 1) *)
(* Proof:
   By induction on (c - k).
   Base: (0 = c - k) ==> (n ** (order_search m n c k) MOD m = 1)
      Let t = order_search m n c k.
      Note 0 = c - k means c <= k      by SUB_EQ_0
      Thus k = c                       by c <= k, k <= c
       ==> t = c                       by order_search_id
        or n ** t MOD m = 1            by (n ** c) MOD m = 1
   Step: !c k. (v = c - k) /\ k < c ==> (n ** (order_search m n c k) MOD m = 1)
         ==> SUC v = c - k ==> (n ** (order_search m n c k) MOD m = 1)
      Let t = order_search m n c k.
      If n ** k MOD m = 1,
         Then t = k                    by order_search_alt, k < c
           so n ** t MOD m = 1         by n ** k MOD m = 1 (if condition)
      If n ** k MOD m <> 1,
         Then t = order_search m n c (k + 1)   by order_search_alt, k < c
         Note SUC v = c - k means k < c        by SUC_POS
           or v + 1 = c - k, or
                  v = c - (k + 1)      by arithmetic
         Also k + 1 <= c               by k < c
           If c = k + 1,
              Then t = order_search m n c c
                     = c               by order_search_id
                so n ** t MOD m = 1    by n ** c MOD m = 1 (given)
           If c <> k + 1,
              Then k + 1 < c           by k < c
               ==> n ** t MOD m = 1    by induction hypothesis, k + 1 < c
*)
val order_search_property = store_thm(
  "order_search_property",
  ``!m n c k. k <= c /\ ((n ** c) MOD m = 1) ==> (n ** (order_search m n c k) MOD m = 1)``,
  rpt strip_tac >>
  Induct_on `c - k` >| [
    rpt strip_tac >>
    `k = c` by decide_tac >>
    rw[order_search_id],
    rpt strip_tac >>
    Cases_on `n ** k MOD m = 1` >-
    rw[order_search_success] >>
    `order_search m n c k = order_search m n c (k + 1)` by rw[Once order_search_alt] >>
    `k + 1 <= c /\ (v = c - (k + 1))` by decide_tac >>
    Cases_on `c = k + 1` >-
    rw[order_search_id] >>
    rw[]
  ]);

(* Theorem: k <= c ==> !j. k <= j /\ j < order_search m n c k ==> n ** j MOD m <> 1 *)
(* Proof:
   By contradiction, suppose some j with (n ** j MOD m = 1).
   Let t = order_search m n c k.
   If k = c,
      Then t = k                     by order_search_id
       But j < t = k                 by j < order_search m n c k (given)
      This contradicts k <= j.
   If k <> c,
   Then k < c                        by k <= c, k <> c.
   Use induction on (j - k).
   Base: 0 = j - k /\ k <= j ==> F
      Note 0 = j - k means j <= k.
      Thus j = k                     by j <= k, k <= j.
        so order_search m n c k = k  by order_search_success, k < c, n ** j MOD m = 1
       But j < order_search m n c k,
        or j < j, which is false     by LESS_REFL
   Step: !j k. (v = j - k) /\ k < c /\ k <= j /\ j < order_search m n c k ==> F ==>
         SUC v = j - k /\ k < c /\ k <= j /\ j < order_search m n c k ==> F
      Note j < t                     by j < order_search m n c k
      If n ** k MOD m = 1,
         Then t = k                  by order_search_alt, k < c
         Thus j < t = k              by j < order_search m n c k
         This contradicts k <= j.
      If n ** k MOD m <> 1,
         Then t = order_search m n c (k + 1)  by order_search_alt, k < c [1]
         Note t <= c                    by order_search_upper, MAX_DEF, k < c.
           so j < c                     by LESS_LESS_EQ_TRANS
          ==> order_search m n c j = j  by order_search_success, j < c [2]

         Note SUC v = j - k means k < j       by SUC_POS
           or v + 1 = j - k, or
                  v = j - (k + 1)    by arithmetic
         Also k + 1 <= j             by k < j
           If j = k + 1,
              Then t = order_search m n c j   by [1], j = k + 1
                     = j                      by [2]
                or j < j, which is false      by LESS_REFL, j < t.
           If j <> k + 1,
              Then k + 1 < j         by k < j
                or k + 1 < c         by j < c
              Thus giving F          by induction hypothesis
*)
val order_search_minimal = store_thm(
  "order_search_minimal",
  ``!m n c k. k <= c ==> !j. k <= j /\ j < order_search m n c k ==> n ** j MOD m <> 1``,
  rpt strip_tac >>
  Cases_on `k = c` >| [
    `order_search m n c k = k` by rw[order_search_id] >>
    decide_tac,
    `k < c` by decide_tac >>
    fs[] >>
    Induct_on `j - k` >| [
      rpt strip_tac >>
      `j = k` by decide_tac >>
      metis_tac[order_search_success, DECIDE``~(n < n)``],
      rpt strip_tac >>
      Cases_on `n ** k MOD m = 1` >| [
        `order_search m n c k = k` by rw[order_search_success] >>
        decide_tac,
        `j < c` by metis_tac[order_search_upper, MAX_DEF, LESS_LESS_EQ_TRANS] >>
        `order_search m n c j = j` by rw[order_search_success] >>
        `order_search m n c k = order_search m n c (k + 1)` by rw[Once order_search_alt] >>
        `k + 1 <= j /\ (v = j - (k + 1))` by decide_tac >>
        Cases_on `j = k + 1` >-
        metis_tac[DECIDE``~(n < n)``] >>
        `k + 1 < c` by decide_tac >>
        metis_tac[]
      ]
    ]
  ]);

(* Theorem: order_compute m n = ordz m n *)
(* Proof:
   By order_compute_alt, this is to show:
   (1) m <> 0 /\ coprime m n ==> order_search m (n MOD m) (phi m) 1 = ordz m n
       Let k = order_search m (n MOD m) (phi m) 1.
       Note 1 <= k                  by order_search_lower
       If m = 1,
          Note k <= MAX (phi 1) 1   by order_search_upper
                  = MAX 1       1   by phi_1
                  = 1               by MAX_DEF
          Thus k = 1                by 1 <= k, k <= 1
                 = ordz 1 n         by ZN_order_mod_1
       If m <> 1,
          Then 1 < m                by 0 < m, m <> 1
           and 0 < k                by 1 <= k
           Now 0 < phi m            by phi_pos, 0 < m
            or 1 <= phi m           by 0 < phi m

          Note coprime m (n MOD m)      by coprime_mod, 0 < m
           and n MOD m < m              by MOD_LESS, 0 < m
          Also 0 < n MOD m              by MOD_NONZERO_WHEN_GCD_ONE, 1 < m
           and (n MOD m) ** (phi m) MOD m = 1       by Euler_Fermat_eqn, phi_eq_totient, 1 < m
           ==> ((n MOD m) ** k) MOD m = 1           by order_search_property, 1 <= phi m
           and !j. 1 <= j /\ j < k ==> ((n MOD m) ** j) MOD m <> 1  by order_search_minimal, 1 <= phi m
          Thus k = ordz m (n MOD m)                 by ZN_order_test_1
                 = ordz m n                         by ZN_order_mod, 0 < m
   (2) m <> 0 /\ gcd m n <> 1 ==> 0 = ordz m n
       Note 0 < m                     by arithmetic
       Thus ordz m n = 0              by ZN_order_eq_0, 0 < m.
*)
val order_compute_eqn = store_thm(
  "order_compute_eqn",
  ``!m n. order_compute m n = ordz m n``,
  rw[order_compute_alt] >| [
    `0 < m` by decide_tac >>
    qabbrev_tac `k = order_search m (n MOD m) (phi m) 1` >>
    `1 <= k` by rw[order_search_lower, Abbr`k`] >>
    Cases_on `m = 1` >| [
      `k <= 1` by metis_tac[order_search_upper, phi_1, MAX_DEF] >>
      rw[ZN_order_mod_1],
      `0 < k /\ 1 < m` by decide_tac >>
      `0 < phi m` by rw[phi_pos] >>
      `1 <= phi m` by decide_tac >>
      `coprime m (n MOD m)` by rw[coprime_mod] >>
      `n MOD m < m` by rw[MOD_LESS] >>
      `0 < n MOD m` by rw[MOD_NONZERO_WHEN_GCD_ONE] >>
      `(n MOD m) ** (phi m) MOD m = 1` by rw[Euler_Fermat_eqn, phi_eq_totient] >>
      `((n MOD m) ** k) MOD m = 1` by rw[order_search_property, Abbr`k`] >>
      `!j. 0 < j /\ j < k ==> ((n MOD m) ** j) MOD m <> 1`
           by metis_tac[order_search_minimal, DECIDE``1 <= n <=> 0 < n``] >>
      `k = ordz m (n MOD m)` by rw[ZN_order_test_1] >>
      `_ = ordz m n` by rw[ZN_order_mod] >>
      rw[]
    ],
    rw[ZN_order_eq_0]
  ]);

(* ------------------------------------------------------------------------- *)
(* Efficient Order Computation                                               *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:

Input: m, n with 1 < m, 0 < n
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

if ~(coprime m n) return 0    // initial check
// For coprime m n, ordz m (n MOD m) is a divisor of (phi m) by Euler-Fermat Theorem.
// Search upwards for least index j
j <- 1                        // initial index
c <- phi m                    // recompute constant
n <- n MOD n                  // reduce n, by ordz m n = ordz m (n MOD m)
while (j <= c) {
   if (j divides c) and (n ** j = 1 (mod m)) return j  // test j
   j <- j + 1                                          // increment j
}
return 0  // unreachable, unless no initial coprime check.

*)

(* A method to compute ordz m n:
Step 1: if (gcd m n <> 1) then 0
Step 2: By Euler-Fermat theorem, ordz m n = ordz m (n MOD m) is a divisor of (phi m).
        Just search from j = 1 to (phi m),
        If exp_mod_compute n j m = 1, return j.
        Search is upwards for the first (least) index j.
*)

(* Question: How to show the number of steps is bounded? *)

(* Formulate a recursive search for the least index, not using WHILE loop. *)
Definition ordz_search_def:
  ordz_search m n c k =
  (* search is from k to maximum c *)
  if c <= k then k (* when k reaches c, k = c, must divide c, and exp_mod_compute n c m = 1 always. *)
  else if k divides c /\ (exp_mod_compute n k m = 1) then k (* that is, found k such that (n ** k) MOD m = 1 *)
  else ordz_search m n c (k + 1) (* current k is not suitable, try k + 1 instead. *)
Termination
  WF_REL_TAC `measure (λ(m,n,c,k). c - k)`
End
(*
val ordz_search_def = |- !n m k c. ordz_search m n c k =
     if c <= k then k
     else if k divides c /\ (exp_mod_compute n k m = 1) then k
     else ordz_search m n c (k + 1): thm
*)

(* Compute ordz m n *)
val ordz_fast_def = Define`
    ordz_fast m n =
         if n = 0 then ordz m 0  (* order is defined for nonzero only *)
    else if m = 0 then ordz m n  (* MOD 0 is undefined *)
    else if (gcd_compute m n = 1) (* For coprimes, search from 1 ... *)
         then ordz_search m (n MOD m) (phi_compute m) 1 (* ordz m n = ordz m (n MOD m), divisor of phi m *)
         else 0 (* not coprime: order is 0 *)
`;

(* Examples:
> EVAL ``ordz_fast 10 3``; --> 4
> EVAL ``ordz_fast 10 4``; --> 0
> EVAL ``ordz_fast 10 7``; --> 4
> EVAL ``ordz_fast 10 19``; --> 2
> EVAL ``ordz_fast 10 1``; --> 1

> EVAL ``phi_compute 10``; --> 4

Indeed, (ordz m n) is a divisor of (phi m).
Since phi(10) = 4, ordz 10 n is a divisior of 4.
*)

(* Theorem: ordz_search m n c k = if c <= k then k
            else if k divides c /\ ((n ** k) MOD m = 1) then k else ordz_search m n c (k + 1) *)
(* Proof: by ordz_search_def, exp_mod_compute_eqn *)
val ordz_search_alt = store_thm(
  "ordz_search_alt",
  ``!m n c k. ordz_search m n c k = if c <= k then k
             else if k divides c /\ ((n ** k) MOD m = 1) then k else ordz_search m n c (k + 1)``,
  rw[Once ordz_search_def, exp_mod_compute_eqn]);

(* Theorem: ordz_fast m n = if n = 0 then ordz m 0
                               else if m = 0 then ordz m n
                               else if coprime m n then ordz_search m (n MOD m) (phi m) 1 else 0 *)
(* Proof: by ordz_fast_def, gcd_compute_eqn, phi_compute_eqn *)
val ordz_fast_alt = store_thm(
  "ordz_fast_alt",
  ``!m n. ordz_fast m n =
     if n = 0 then ordz m 0
     else if m = 0 then ordz m n
     else if coprime m n then ordz_search m (n MOD m) (phi m) 1 else 0``,
  rw[ordz_fast_def, gcd_compute_eqn, phi_compute_eqn]);

(* Theorem: ordz_search m n c c = c *)
(* Proof: ordz_search_def *)
val ordz_search_id = store_thm(
  "ordz_search_id",
  ``!m n c. ordz_search m n c c = c``,
  rw[Once ordz_search_def]);

(* Theorem: c <= k ==> (ordz_search m n c k = k) *)
(* Proof: ordz_search_def *)
val ordz_search_over = store_thm(
  "ordz_search_over",
  ``!m n c k. c <= k ==> (ordz_search m n c k = k)``,
  rw[Once ordz_search_def]);

(* Theorem: k < c /\ k divides c /\ ((n ** k) MOD m = 1) ==> (ordz_search m n c k = k) *)
(* Proof: by ordz_search_alt *)
val ordz_search_success = store_thm(
  "ordz_search_success",
  ``!m n c k. k < c /\ k divides c /\ ((n ** k) MOD m = 1) ==> (ordz_search m n c k = k)``,
  rw[Once ordz_search_alt]);

(* Theorem: k <= ordz_search m n c k *)
(* Proof:
   By induction on (c - k).
   Base: (0 = c - k) ==> k <= ordz_search m n c k
      Note 0 = c - k means c <= k,
        or c <= k                      by SUB_EQ_0
           ordz_search m n c k
         = k                           by ordz_search_alt, ~(k < c)
         >= k                          by LESS_OR_EQ
   Step: !c k. (v = c - k) ==> k <= ordz_search m n c k ==>
         (SUC v = c - k) ==> k <= ordz_search m n c k
      Note SUC v = c - k means k < c   by SUC_POS
        or v + 1 = c - k, or
               v = c - (k + 1)         by arithmetic
        If (k divides c /\ (n ** k MOD m = 1)),
           ordz_search m n c k
         = k                           by ordz_search_alt, k < c
         >= k                          by LESS_OR_EQ
        If ~(k divides c /\ (n ** k MOD m = 1)),
           ordz_search m n c k
         = ordz_search m n c (k + 1)   by ordz_search_alt, k < c
         >= k + 1                      by induction hypothesis
         >= k                          by arithmetic
*)
val ordz_search_lower = store_thm(
  "ordz_search_lower",
  ``!m n c k. k <= ordz_search m n c k``,
  rpt strip_tac >>
  Induct_on `c - k` >| [
    rpt strip_tac >>
    rw[Once ordz_search_alt],
    rpt strip_tac >>
    `v = c - (k + 1)` by decide_tac >>
    rw[Once ordz_search_alt] >>
    metis_tac[LESS_EQ_TRANS, DECIDE``k <= k + 1``]
  ]);

(* Theorem: ordz_search m n c k <= MAX k c *)
(* Proof:
   By induction on (c - k).
   Base: (0 = c - k) ==> ordz_search m n c k <= MAX k c
      Note 0 = c - k means c <= k,
        or c <= k                      by SUB_EQ_0
           ordz_search m n c k
         = k                           by ordz_search_alt, ~(k < c)
         = MAX k c                     by c <= k
         <= MAX k c                    by LESS_OR_EQ
   Step: !c k. (v = c - k) ==> ordz_search m n c k <= MAX k c ==>
         (SUC v = c - k) ==> ordz_search m n c k <= MAX k c
      Note SUC v = c - k means k < c   by SUC_POS
        or v + 1 = c - k, or
               v = c - (k + 1)         by arithmetic
        If (k divides c /\ (n ** k MOD m = 1)),
           ordz_search m n c k
         = k                           by ordz_search_alt, k < c
         <= c                          by LESS_OR_EQ
        If ~(k divides c /\ (n ** k MOD m = 1)),
           ordz_search m n c k
         = ordz_search m n c (k + 1)   by ordz_search_alt, k < c
         <= MAX (k + 1) c              by induction hypothesis
         <= MAX k c                    by k < c ==> (k + 1) <= c
        Indeed, MAX (k + 1) c = c = MAX k c   by MAX_DEF
*)
val ordz_search_upper = store_thm(
  "ordz_search_upper",
  ``!m n c k. ordz_search m n c k <= MAX k c``,
  rpt strip_tac >>
  Induct_on `c - k` >| [
    rpt strip_tac >>
    rw[Once ordz_search_alt],
    rpt strip_tac >>
    `v = c - (k + 1)` by decide_tac >>
    `k <= MAX k c` by rw[] >>
    rw_tac bool_ss[Once ordz_search_alt] >>
    `MAX (k + 1) c = MAX k c` by rw[MAX_DEF] >>
    metis_tac[]
  ]);

(* Theorem: k <= c /\ ((n ** c) MOD m = 1) ==>
            (ordz_search m n c k) divides c /\ (n ** (ordz_search m n c k) MOD m = 1) *)
(* Proof:
   Let t = order_search m n c k.
   If k = c,
      Then t = c                       by ordz_search_id
        so t divides c                 by DIVIDES_REFL, t = c
       and n ** t MOD m = 1            by (n ** c) MOD m = 1
   If k <> c,
   Then k < c                          by arithmetic
   By induction on (c - k).
   Base: (0 = c - k) ==> (ordz_search m n c k) divides c /\ (n ** (ordz_search m n c k) MOD m = 1)
      Note 0 = c - k means c <= k
        or c <= k                      by SUB_EQ_0
      This contradicts k < c.
   Step: !c k. (v = c - k) /\ k <= c ==> (ordz_search m n c k) divides c /\ (n ** (ordz_search m n c k) MOD m = 1)
         ==> SUC v = c - k ==> (ordz_search m n c k) divides c /\ (n ** (ordz_search m n c k) MOD m = 1)
      If (k divides c /\ (n ** k MOD m = 1)),
         Then t = k                    by ordz_search_alt, k < c
           so t divides c              by k divides c
          and n ** t MOD m = 1         by n ** k MOD m = 1
      If ~(k divides c /\ (n ** k MOD m = 1)),
         Then t = ordz_search m n c (k + 1)   by ordz_search_alt, k < c
         Note SUC v = c - k means k < c        by SUC_POS
           or v + 1 = c - k, or
                  v = c - (k + 1)      by arithmetic
         Also k + 1 <= c               by k < c
           If c = k + 1,
              Then t = ordz_search m n c c
                     = c               by ordz_search_id
               and c divides c         by DIVIDES_REFL
               and n ** c MOD m = 1    by given
           If c <> k + 1,
              Then k + 1 < c           by k < c
               ==> t divides c
               and n ** t MOD m = 1    by induction hypothesis, k + 1 < c
*)
val ordz_search_property = store_thm(
  "ordz_search_property",
  ``!m n c k. k <= c /\ ((n ** c) MOD m = 1) ==>
    (ordz_search m n c k) divides c /\ (n ** (ordz_search m n c k) MOD m = 1)``,
  ntac 5 strip_tac >>
  Cases_on `k = c` >-
  metis_tac[ordz_search_id, DIVIDES_REFL] >>
  `k < c` by decide_tac >>
  fs[] >>
  Induct_on `c - k` >| [
    ntac 5 strip_tac >>
    decide_tac,
    ntac 5 strip_tac >>
    Cases_on `k divides c /\ (n ** k MOD m = 1)` >-
    rw[ordz_search_success] >>
    `ordz_search m n c k = ordz_search m n c (k + 1)` by rw[Once ordz_search_alt] >>
    `k + 1 <= c /\ (v = c - (k + 1))` by decide_tac >>
    Cases_on `c = k + 1` >-
    rw[ordz_search_id] >>
    rw[]
  ]);

(* Theorem: k <= c ==> !j. k <= j /\ j < ordz_search m n c k ==> ~(j divides c /\ (n ** j MOD m = 1)) *)
(* Proof:
   By contradiction, suppose some j divides c /\ (n ** j MOD m = 1).
   Let t = ordz_search m n c k.
   If k = c,
      Then t = k                       by ordz_search_id
       But j < t = k                   by j < order_search m n c k (given)
      This contradicts k <= j.
   If k <> c,
   Then k < c                          by k <= c, k <> c.
   Use induction on (j - k).
   Base: 0 = j - k /\ k <= j ==> F
      Note 0 = j - k means j <= k.
      Thus j = k                       by j <= k, k <= j.
        so ordz_search m n c k = k     by ordz_search_success, k < c, j divides c, n ** j MOD m = 1
       But j < ordz_search m n c k,
        or j < j, which is false       by LESS_REFL
   Step: !j k. (v = j - k) /\ k < c /\ k <= j /\ j < ordz_search m n c k ==> F ==>
         SUC v = j - k /\ k < c /\ k <= j /\ j < ordz_search m n c k ==> F
      Note j < t                       by j < ordz_search m n c k
      If (k divides c /\ (n ** k MOD m = 1)),
         Then t = k                    by ordz_search_alt, k < c
         Thus j < t = k                by j < ordz_search m n c k
         This contradicts k <= j.
      If ~(k divides c /\ (n ** k MOD m = 1)),
         Then t = ordz_search m n c (k + 1)   by ordz_search_alt, k < c [1]
         Note t <= c                   by ordz_search_upper, MAX_DEF, k < c.
           so j < c                    by LESS_LESS_EQ_TRANS
          ==> ordz_search m n c j = j  by ordz_search_success, j < c [2]

         Note SUC v = j - k means k < j       by SUC_POS
           or v + 1 = j - k, or
                  v = j - (k + 1)      by arithmetic
         Also k + 1 <= j               by k < j
           If j = k + 1,
              Then t = ordz_search m n c j    by [1], j = k + 1
                     = j                      by [2]
                or j < j, which is false      by LESS_REFL, j < t.
           If j <> k + 1,
              Then k + 1 < j           by k < j
                or k + 1 < c           by j < c
              Thus giving F            by induction hypothesis
*)
val ordz_search_minimal = store_thm(
  "ordz_search_minimal",
  ``!m n c k. k <= c ==> !j. k <= j /\ j < ordz_search m n c k ==> ~(j divides c /\ (n ** j MOD m = 1))``,
  rpt strip_tac >>
  Cases_on `k = c` >| [
    `ordz_search m n c k = k` by rw[ordz_search_id] >>
    decide_tac,
    `k < c` by decide_tac >>
    fs[] >>
    Induct_on `j - k` >| [
      rpt strip_tac >>
      `j = k` by decide_tac >>
      metis_tac[ordz_search_success, DECIDE``~(n < n)``],
      rpt strip_tac >>
      Cases_on `k divides c /\ (n ** k MOD m = 1)` >| [
        `ordz_search m n c k = k` by rw[ordz_search_success] >>
        decide_tac,
        `j < c` by metis_tac[ordz_search_upper, MAX_DEF, LESS_LESS_EQ_TRANS] >>
        `ordz_search m n c j = j` by rw[ordz_search_success] >>
        `ordz_search m n c k = ordz_search m n c (k + 1)` by rw[Once ordz_search_alt] >>
        `k + 1 <= j /\ (v = j - (k + 1))` by decide_tac >>
        Cases_on `j = k + 1` >-
        metis_tac[DECIDE``~(n < n)``] >>
        `k + 1 < c` by decide_tac >>
        metis_tac[]
      ]
    ]
  ]);

(* Theorem: ordz_fast m n = ordz m n *)
(* Proof:
   By ordz_fast_alt, this is to show:
   (1) m <> 0 /\ coprime m n ==> ordz_search m (n MOD m) (phi m) 1 = ordz m n
       Note ~(m <= 1) means 1 < m     by NOT_LESS_EQUAL
       Let k = ordz_search m (n MOD m) (phi m) 1.
       Note 1 <= k           by ordz_search_lower
       If m = 1,
          Note k <= MAX (phi 1) 1   by ordz_search_upper
                  = MAX 1       1   by phi_1
                  = 1               by MAX_DEF
          Thus k = 1                by 1 <= k, k <= 1
                 = ordz 1 n         by ZN_order_mod_1
       If m <> 1,
          Then 1 < m                by 0 < m, m <> 1
           and 0 < k                by 1 <= k
           Now 0 < phi m            by phi_pos, 0 < m
            or 1 <= phi m           by 0 < phi m

          Note coprime m (n MOD m)      by coprime_mod, 0 < m
           and n MOD m < m              by MOD_LESS, 0 < m
          Also 0 < n MOD m              by MOD_NONZERO_WHEN_GCD_ONE, 1 < m
           and (n MOD m) ** (phi m) MOD m = 1         by Euler_Fermat_eqn, phi_eq_totient, 1 < m
           ==> ((n MOD m) ** k) MOD m = 1             by ordz_search_property, 1 <= phi m
           and !j. 1 <= j /\ j < k /\ j divides (phi m)
                   ==> ((n MOD m) ** j) MOD m <> 1    by ordz_search_minimal, 1 <= phi m
            or !j. 0 < j /\ j < k /\ j divides (phi m)
                   ==> ((n MOD m) ** j) MOD m <> 1    by arithmetic
          Thus k = ordz m (n MOD m)                   by ZN_order_test_2
                 = ordz m n                           by ZN_order_mod, 0 < m
   (2) m <> 0 /\ gcd m n <> 1 ==> 0 = ordz m n
       Note ~(m <= 1) means 1 < m     by NOT_LESS_EQUAL
       Thus ordz m n = 0              by ZN_order_eq_0, 0 < m.
*)
val ordz_fast_eqn = store_thm(
  "ordz_fast_eqn",
  ``!m n. ordz_fast m n = ordz m n``,
  rw[ordz_fast_alt] >| [
    `0 < m` by decide_tac >>
    qabbrev_tac `k = ordz_search m (n MOD m) (phi m) 1` >>
    `1 <= k` by rw[ordz_search_lower, Abbr`k`] >>
    Cases_on `m = 1` >| [
      `k <= 1` by metis_tac[ordz_search_upper, phi_1, MAX_DEF] >>
      rw[ZN_order_mod_1],
      `0 < k /\ 1 < m` by decide_tac >>
      `0 < phi m` by rw[phi_pos] >>
      `1 <= phi m` by decide_tac >>
      `coprime m (n MOD m)` by rw[coprime_mod] >>
      `n MOD m < m` by rw[MOD_LESS] >>
      `0 < n MOD m` by rw[MOD_NONZERO_WHEN_GCD_ONE] >>
      `(n MOD m) ** (phi m) MOD m = 1` by rw[Euler_Fermat_eqn, phi_eq_totient] >>
      `((n MOD m) ** k) MOD m = 1` by rw[ordz_search_property, Abbr`k`] >>
      `!j. 0 < j /\ j < k /\ j divides (phi m) ==> ((n MOD m) ** j) MOD m <> 1`
           by metis_tac[ordz_search_minimal, DECIDE``1 <= n <=> 0 < n``] >>
      `k = ordz m (n MOD m)` by rw[ZN_order_test_2] >>
      `_ = ordz m n` by rw[ZN_order_mod] >>
      rw[]
    ],
    rw[ZN_order_eq_0]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
