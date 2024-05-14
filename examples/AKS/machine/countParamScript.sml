(* ------------------------------------------------------------------------- *)
(* AKS parameter from Count Monad                                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countParam";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     logrootTheory pairTheory optionTheory listRangeTheory numberTheory
     combinatoricsTheory primeTheory;

open ringTheory;

open countMonadTheory countMacroTheory;
open countBasicTheory countPowerTheory;

open countOrderTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;

open computeParamTheory; (* for param_search_result *)

open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = intLib.deprecate_int ();

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * (n :num)``);

(* ------------------------------------------------------------------------- *)
(* AKS parameter with Count Monad Documentation                              *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   AKS parameter search in Monadic style:
   param_seekM_def     |- !n m k c. param_seekM m c n k =
                                    do
                                      k0 <- zeroM k;
                                      if k0 then unit bad
                                      else
                                        do
                                          b0 <- leqM c k;
                                          if b0 then unit bad
                                          else
                                            do
                                              r <- modM n k;
                                              r0 <- zeroM r;
                                              if r0 then unit (nice k)
                                              else
                                                do
                                                  z <- ordzM k n;
                                                  b1 <- leqM m z;
                                                  if b1 then unit (good k)
                                                  else do j <- incM k; param_seekM m c n j od
                                                od
                                            od
                                        od
                                    od
   paramM_def          |- !n. paramM n =
                              do
                                m0 <- ulogM n;
                                b0 <- zeroM m0;
                                b1 <- oneM m0;
                                if b0 \/ b1 then unit (nice n)
                                else
                                  do
                                    m <- sqM m0;
                                    v0 <- expM m0 5;
                                    d <- halfM v0;
                                    c <- addM d 2;
                                    param_seekM m c n 2
                                  od
                              od
#  param_seekM_value   |- !m c n k. valueOf (param_seekM m c n k) =
                                    if k = 0 then bad else param_seek m c n k
#  paramM_value        |- !n. valueOf (paramM n) = param n
   paramM_value_alt    |- !n. valueOf (paramM n) = aks_param n

   param_seekM_steps_thm
                       |- !m c n k. stepsOf (param_seekM m c n k) = size k +
                                    if k = 0 then 0
                                    else size (MAX c k) + size (c - k) + if c <= k then 0
                                    else size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                                    else stepsOf (ordzM k n) + size (MAX m (ordz k n)) +
                                         size (m - ordz k n) + if m <= ordz k n then 0
                                    else size k + stepsOf (param_seekM m c n (k + 1))
   paramM_steps_thm    |- !n. stepsOf (paramM n) =
                                 stepsOf (ulogM n) + TWICE (size (ulog n)) +
                                 if n <= 2 then 0
                                 else size (ulog n) ** 2 + TWICE (size (ulog n ** 5)) +
                                      size (MAX (HALF (ulog n ** 5)) 2) + stepsOf (expM (ulog n) 5) +
                                      stepsOf (param_seekM (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2)
   param_seekM_steps_by_inc_loop
                       |- !m c n. (let quit k = if k = 0 then 1 else 1 + TWICE (size k) ;
                                       body k = size k +
                                         if k = 0 then 0
                                         else size c + size (c - k) + size n * size k +
                                              size (n MOD k) + if n MOD k = 0 then 0
                                         else stepsOf (ordzM k n) + size (MAX m (ordz k n)) +
                                              size (m - ordz k n) + if m <= ordz k n then 0 else size k ;
                                       exit k = ((k = 0) \/ (n MOD k = 0) \/ m <= ordz k n)
                                    in !k. stepsOf (param_seekM m c n k) =
                                           if c <= k then quit k else body k +
                                           if exit k then 0 else stepsOf (param_seekM m c n (k + 1)))
   param_seekM_body_upper
                       |- !m c n. (let body k = size k +
                                         if k = 0 then 0
                                         else size c + size (c - k) + size n * size k +
                                              size (n MOD k) + if n MOD k = 0 then 0
                                         else stepsOf (ordzM k n) + size (MAX m (ordz k n)) +
                                              size (m - ordz k n) + if m <= ordz k n then 0 else size k
                                    in !k. body k <=
                                           TWICE (size m) + TWICE (size c) + 4 * size k +
                                           size n * size k + 27 * k * size n * size k ** 7)
   param_seekM_body_bound
                       |- !m c n. (let body k = size k +
                                         if k = 0 then 0
                                         else size c + size (c - k) + size n * size k +
                                              size (n MOD k) + if n MOD k = 0 then 0
                                         else stepsOf (ordzM k n) + size (MAX m (ordz k n)) +
                                              size (m - ordz k n) + if m <= ordz k n then 0 else size k
                                    in !k. body k <=
                                           36 * MAX 1 k * size m * size c * size n * size k ** 7)
   param_seekM_steps_upper
                       |- !m c n k. stepsOf (param_seekM m c n k) <=
                                    1 + TWICE (size (MAX c k)) +
                                        36 * (c - k) * c * size m * size n * size c ** 8
   param_seekM_steps_bound
                       |- !m c n k. stepsOf (param_seekM m c n k) <=
                                    39 * MAX 1 (c - k) * MAX 1 c * size (MAX c k) * size m * size n *
                                         size c ** 7
   paramM_steps_upper  |- !n. stepsOf (paramM n) <=
                                 19 * size n + 16904 * size n ** 2 + 1348963434 * size n ** 20
   paramM_steps_bound  |- !n. stepsOf (paramM n) <= 1348980357 * size n ** 20
   paramM_steps_O_poly |- stepsOf o paramM IN O_poly 20
   paramM_steps_big_O  |- stepsOf o paramM IN big_O (\n. ulog n ** 20)
   paramM_thm          |- !n. (valueOf (paramM n) = param n) /\
                              stepsOf o paramM IN big_O (\n. ulog n ** 20)
*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* for EVAL IFm *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* EVAL IFm must be in current script, e.g. EVAL ``expn 1 2 3``; *)

(* ------------------------------------------------------------------------- *)
(* AKS parameter search in Monadic style                                     *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:
   Given n, and a maximum m, and a count k to cutoff c,
   find a modulus k such that (ordz k n >= m), which is good,
   or a value k that divides n, which is nice,
   or k exceeds cutoff c and still no nice or good, then bad.

   if m = 0 or m = 1, nice n       // nice n
   if k = 0, bad                   // exclude k = 0
   loop:
      if c <= k, return bad        // unreachable
      r <- n MOD k                 // compute remainder of n divided by k
      if r = 0, return nice k      // found a factor k of n
      z <- ordz k n                // compute order of n in modulus k
      if m <= z, return good k     // found a good modulus k
      k <- k + 1
      goto loop

   Note: k is at least 2 in order for n MOD k and ordz k n to be reasonable.
   Note: k needs to be increasing to guarantee the coprime feature when not dividing.
*)

(*
> param_seek_def;
val it = |- !n m k c.
          param_seek m c n k =
          if c <= k then bad
          else if n MOD k = 0 then nice k
          else if m <= ordz k n then good k
          else param_seek m c n (k + 1): thm
*)
(* Although param_seek_def does not check k = 0, as the caller ensures k = 2,
param_seekM_def has to check k = 0, in order that complexity analysis can be
carried out independently on (param_seek m c n k), for all values of k.
This is particular true when going deeper into !k. body k <= cover k, and MONO cover.
If (param_seek m c n 0) is undefined, it is difficult to bound (body k),
unless we develop a theory of partial cover and partial MONO, to derive partial bounds.
*)

(* Define the parameter seek loop *)
Definition param_seekM_def:
    param_seekM m c n k =
      do
         k0 <- zeroM k;
         if k0 then return bad
         else do
               b0 <- leqM c k;
              if b0 then return bad
              else do (* check if k is a factor of n *)
                     r <- modM n k;
                     r0 <- zeroM r;
                     if r0 then return (nice k)
                     else do (* check if ordz k n is big enough *)
                            z <- ordzM k n;
                            b1 <- leqM m z;
                            if b1 then return (good k)
                            else do
                                  j <- incM k;
                                  param_seekM m c n j;
                                od
                          od
                     od
              od
      od
Termination WF_REL_TAC `measure (λ(m,c,n,k). c - k)` >> simp[]
End

(*
> EVAL ``param_seekM 25 31 31 2``;
val it = |- param_seekM 31 25 31 31 = (good 29,Count 38712): thm

Step 2: Use 31 to find a suitable k to make the modulus x^k - 1
AKS parameter search: n=31, m=25
AKS parameter search: max=1562
AKS parameter k=29
*)

(*
> param_def;
val it = |- !n. param n =
                (let m = SQ (ulog n) ;
                     c = 2 + HALF (ulog n ** 5)
                  in if n <= 2 then nice n else param_seek m c n 2): thm
*)

(* To compute the AKS parameter k *)
val paramM_def = Define`
    paramM n =
      do
        m0 <- ulogM n;
        b0 <- zeroM m0;
        b1 <- oneM m0;
        if b0 \/ b1 then unit (nice n) (* m0 <= 1 means n <= 2 *)
        else do
                m <- sqM m0; (* make SQ (ulog n) *)
                v0 <- expM m0 5;
                d <- halfM v0; (* make HALF (ulog n ** 5) *)
                c <- addM d 2; (* make 2 + HALF (ulog n ** 5) *)
                param_seekM m c n 2;
             od
      od
`;

(*
> EVAL ``paramM 31``;
val it = |- paramM 31 = (good 29,Count 39428): thm
*)


(* Theorem: valueOf (param_seekM m c n k) = param_seek m c n k *)
(* Proof: by param_seekM_def, param_seek_def *)
val param_seekM_value = store_thm(
  "param_seekM_value[simp]",
  ``!m c n k. valueOf (param_seekM m c n k) =
             if k = 0 then bad else param_seek m c n k``,
  ho_match_mp_tac (theorem "param_seekM_ind") >>
  rpt strip_tac >>
  (rw[Once param_seekM_def, Once param_seek_def] >> fs[]));

(* Theorem: valueOf (paramM n) = param n *)
(* Proof: by paramM_def, param_alt *)
val paramM_value = store_thm(
  "paramM_value[simp]",
  ``!n. valueOf (paramM n) = param n``,
  (rw[paramM_def, param_alt] >> fs[]));

(* Theorem: valueOf (paramM n) = aks_param n *)
(* Proof: by paramM_value, param_eqn. *)
val paramM_value_alt = store_thm(
  "paramM_value_alt",
  ``!n. valueOf (paramM n) = aks_param n``,
  rw[param_eqn]);

(* This is the most important result for correctness! *)


(* Theorem: stepsOf (param_seekM m c n k) = size k +
     if k = 0 then 0
     else size (MAX c k) + size (c - k) + if c <= k then 0
     else size n * size k + size (n MOD k) + if n MOD k = 0 then 0
     else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if (m <= ordz k n) then 0
     else size k + stepsOf (param_seekM m c n (k + 1)) *)
(* Proof:
     stepsOf (param_seekM m c n k)
   = stepsOf (zeroM k) + if k = 0 then 0
     else stepsOf (leqM c k) + if c <= k then 0
     else stepsOf (modM n k) + stepsOf (zeroM (n MOD k)) + if (n MOD k = 0) then 0
     else stepsOf (ordzM k n) + stepsOf (leqM m (ordz k n)) + if (m <= ordz k n) then 0
     else stepsOf (incM k) + stepsOf (param_seekM m c n (k + 1))  by param_seekM_def
   = size k + if k = 0 then 0
     else size (MAX c k) + size (c - k) + if c <= k then 0            by size_max
     else size n * size k + size (n MOD k) + if n MOD k = 0 then 0    by modM_steps, 0 < k
     else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if (m <= ordz k n) then 0
     else size k + stepsOf (param_seekM m c n (k + 1))
   = size k + if k = 0 then 0
     else size (MAX c k) + size (c - k)) + if c <= k then 0
     else size n * size k + size (n MOD k) + if n MOD k = 0 then 0
     else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if (m <= ordz k n) then 0
     else size k + stepsOf (param_seekM m c n (k + 1))
*)
val param_seekM_steps_thm = store_thm(
  "param_seekM_steps_thm",
  ``!m c n k. stepsOf (param_seekM m c n k) = size k +
     if k = 0 then 0
     else size (MAX c k) + size (c - k) + if c <= k then 0
     else size n * size k + size (n MOD k) + if n MOD k = 0 then 0
     else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if (m <= ordz k n) then 0
     else size k + stepsOf (param_seekM m c n (k + 1))``,
  ho_match_mp_tac (theorem "param_seekM_ind") >>
  rpt strip_tac >>
  Cases_on `k = 0` >-
  simp[Once param_seekM_def] >>
  Cases_on `c <= k` >-
  simp[Once param_seekM_def, size_max] >>
  Cases_on `n MOD k = 0` >-
  simp[Once param_seekM_def, size_max] >>
  Cases_on `m <= ordz k n` >-
  simp[Once param_seekM_def, size_max] >>
  fs[Once param_seekM_def, size_max]);

(* Theorem: stepsOf (paramM n) =
            stepsOf (ulogM n) + 2 * size (ulog n) +
            if (n <= 2) then 0
            else (size (ulog n)) ** 2 + 2 * size ((ulog n) ** 5) + size (MAX (HALF ((ulog n) ** 5)) 2) +
                 stepsOf (expM (ulog n) 5) +
                 stepsOf (param_seekM (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2) *)
(* Proof:
     stepsOf (paramM n)
   = stepsOf (ulogM n) +
     stepsOf (zeroM (ulog n)) +
     stepsOf (oneM (ulog n)) + if (ulog n = 0 \/ ulog n = 1) then 0
     else stepsOf (sqM (ulog n)) +
          stepsOf (expM (ulog n) 5) +
          stepsOf (halfM ((ulog n) ** 5)) +
          stepsOf (addM (HALF ((ulog n) ** 5)) 2) +
          stepsOf (param_seekM (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2))  by paramM_def
   = stepsOf (ulogM n) +
     2 * size (ulog n) +
     if (n <= 2) then 0          by ulog_eq_0, ulog_eq_1
     else (size (ulog n)) ** 2 +
          stepsOf (expM (ulog n) 5) + 2 * size ((ulog n) ** 5) +
          size (MAX (HALF ((ulog n) ** 5)) 2) +
          stepsOf (param_seekM (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2)   by size_max
   = stepsOf (ulogM n) + 2 * size (ulog n) +
     if (n <= 2) then 0
     else (size (ulog n)) ** 2 + 2 * size ((ulog n) ** 5) + size (MAX (HALF ((ulog n) ** 5)) 2) +
     stepsOf (expM (ulog n) 5) +
     stepsOf (param_seekM (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2)
*)
val paramM_steps_thm = store_thm(
  "paramM_steps_thm",
  ``!n. stepsOf (paramM n) =
       stepsOf (ulogM n) + 2 * size (ulog n) +
       if (n <= 2) then 0
       else (size (ulog n)) ** 2 +
            2 * size ((ulog n) ** 5) + size (MAX (HALF ((ulog n) ** 5)) 2) +
            stepsOf (expM (ulog n) 5) +
            stepsOf (param_seekM (SQ (ulog n)) (2 + HALF ((ulog n) ** 5)) n 2)``,
  rw[paramM_def, ulog_eq_0, ulog_eq_1, size_max]);

(* Theorem: let quit k = 2 * size m + if m <= 1 then 0 else if k = 0 then 1 else 1 + 2 * size k;
                body k = 2 * size m + if m <= 1 then 0
                   else size k + if k = 0 then 0
                   else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                   else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                   else size k;
                exit k = ((k = 0) \/ (n MOD k = 0) \/ m <= ordz k n)
             in !k. stepsOf (param_seekM m c n k) =
                    if c <= k then quit k
                    else body k + if exit k then 0 else stepsOf (param_seekM m c n (k + 1)) *)
(* Proof:
     stepsOf (param_seekM m c n k)
   = size k + if k = 0 then 0
     else size (MAX c k) + size (c - k) + if c <= k then 0         <-- guard is here
     else size n * size k + size (n MOD k) + if n MOD k = 0 then 0
     else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
     else size k + stepsOf (param_seekM m c n (k + 1))             by param_seekM_steps_thm
   = if c <= k then  -- all these before it
        (size k + if k = 0 then 0 else size (MAX c k) + size (c - k))
     else -- repeat all those before it
        size k + if k = 0 then 0
        else size (MAX c k) + size (c - k) +
             size n * size k + size (n MOD k) + if n MOD k = 0 then 0
             else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
             else size k + stepsOf (param_seekM m c n (k + 1))
   = if c <= k then quit k
     else body k + if exit k then 0 else stepsOf (param_seekM m c n (k + 1))
   where
       quit k
     = size k + if k = 0 then 0 else size k + size 0
     = if k = 0 then size 0 else size k + size k + size 0
     = if k = 0 then 1 else 1 + 2 * size k
       body k, with k < c
     = size k + if k = 0 then 0
       else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
       else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
       else size k
       exit k
     = (k = 0) \/ n MOD k = 0 \/ m <= ordz k n
*)
val param_seekM_steps_by_inc_loop = store_thm(
  "param_seekM_steps_by_inc_loop",
  ``!m c n. let quit k = if k = 0 then 1 else 1 + 2 * size k;
               body k = size k +
                 if k = 0 then 0
                 else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                 else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                 else size k;
               exit k = ((k = 0) \/ (n MOD k = 0) \/ m <= ordz k n)
            in !k. stepsOf (param_seekM m c n k) = if c <= k then quit k
                   else body k + if exit k then 0 else stepsOf (param_seekM m c n (k + 1))``,
  rw_tac std_ss[Once param_seekM_steps_thm] >>
  Cases_on `k = 0` >> simp[Abbr`body`, Abbr`exit`, Abbr`quit`] >>
  (Cases_on `c <= k` >> simp[MAX_DEF]) >>
  `c - k = 0` by decide_tac >>
  rw[] >>
  `c = k` by decide_tac >>
  simp[]);

(*
This puts param_seekM_steps in the category: increasing loop with body cover and exit.
   param_seekM_steps_by_inc_loop:
        !k. loop k = if c <= k then quit k else body k + if exit k then 0 else loop (k + 1)
suitable for: loop_inc_count_cover_exit_le
*)

(* First, work out a cover for the body. *)

(* Theorem: let body k = size k +
                if k = 0 then 0
                else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                else size k
             in !k. body k <=
                    2 * size m + 2 * size c + 4 * size k + size n * size k + 29 * k * size n * size k ** 7 *)
(* Proof:
      body k
    = size k + if k = 0 then 0
      else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
      else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
      else size k                                      by given
   <= size k + size c + size (c - k) + size n * size k + size (n MOD k) +
      stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) +
      if m <= ordz k n then 0 else size k
                                                       by ignoring n MOD k = 0
      Note c - k <= c, so size (c - k) <= size c       by size_monotone_le
       and size (m - ordz k n) <= size m               by size_monotone_le
       and n MOD k < k                                 by MOD_LESS, k <> 0
        so size (n MOD k) <= size k                    by size_monotone_lt
      If m <= ordz k n,
           size (MAX m (ordz k n)) = size (ordz k n)   by MAX_DEF
       now ordz k n <= k                               by ZN_order_le, 0 < k
        so size (MAX m (ordz k n)) <= size k           by size_monotone_le
        but m <= ordz k n gives the last term 0.
      If ~(m <= ordz k n), or ordz k n < m
        so size (MAX m (ordz k n)) = size m            by MAX_DEF
 Thus body k
   <= size k + size c + size c + size n * size k + size k +
      size m + size m + size k + stepsOf (ordzM k n)
    = 2 * size m + 2 * size c + 4 * size k + size n * size k + stepsOf (ordzM k n)

      stepsOf (ordzM k n)
   <= 27 * MAX 1 k * size n * size k ** 7              by ordzM_steps_bound
    = 27 * k * size n * size k ** 7                    by MAX_DEF, k <> 0
 Thus body k
   <= 2 * size m + 2 * size c + 4 * size k + size n * size k + 27 * k * size n * size k ** 7
*)
val param_seekM_body_upper = store_thm(
  "param_seekM_body_upper",
  ``!m c n. let body k = size k +
               if k = 0 then 0
               else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
               else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
               else size k
            in !k. body k <=
                   2 * size m + 2 * size c + 4 * size k + size n * size k + 27 * k * size n * size k ** 7``,
  rw_tac std_ss[] >>
  Cases_on `k = 0` >> simp[Abbr`body`] >>
  `size (c - k) <= size c` by rw[size_monotone_le] >>
  `0 < size k` by rw[] >>
  (Cases_on `n MOD k = 0` >> simp[]) >>
  `size (m - ordz k n) <= size m` by rw[size_monotone_le] >>
  `size (n MOD k) <= size k` by rw[MOD_LESS, size_monotone_lt] >>
  `MAX 1 k = k` by rw[MAX_DEF] >>
  `stepsOf (ordzM k n) <= 27 * k * size n * size k ** 7` by metis_tac[ordzM_steps_bound] >>
  (Cases_on `m <= ordz k n` >> simp[]) >| [
    `MAX m (ordz k n) = ordz k n` by rw[MAX_DEF] >>
    `ordz k n <= k` by rw[ZN_order_le] >>
    `MAX m (ordz k n) <= k` by decide_tac >>
    `size (MAX m (ordz k n)) <= size k` by rw[size_monotone_le] >>
    decide_tac,
    `size (MAX m (ordz k n)) = size m` by rw[MAX_DEF] >>
    decide_tac
  ]);

(* Theorem: let body k = size k +
                 if k = 0 then 0
                 else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                 else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                 else size k
              in body k <= 36 * (MAX 1 k) * size m * size c * size n * size k ** 7 *)
(* Proof:
       body k
    <= 2 * size m + 2 * size c + 4 * size k + size n * size k + 27 * k * size n * size k ** 7
                                               by param_seekM_body_upper
    <= (2 + 2 + 4 + 1 + 27) * k * size m * size c * size n * size k ** 7
                                               by dominant term
     = 36 * k * size m * size c * size n * size k ** 7
   Use (MAX 1 k) to cater for k = 0.
*)
val param_seekM_body_bound = store_thm(
  "param_seekM_body_bound",
  ``!m c n. let body k = size k +
               if k = 0 then 0
               else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
               else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
               else size k
            in !k. body k <= 36 * (MAX 1 k) * size m * size c * size n * size k ** 7``,
  rpt strip_tac >>
  assume_tac param_seekM_body_upper >>
  last_x_assum (qspecl_then [`m`, `c`, `n`] strip_assume_tac) >>
  qabbrev_tac `body = \k. size k +
                 if k = 0 then 0
                 else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                 else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                 else size k` >>
  fs[] >>
  strip_tac >>
  last_x_assum (qspec_then `k` strip_assume_tac) >>
  qabbrev_tac `h = MAX 1 k` >>
  qabbrev_tac `t = size c * size k ** 7 * size m * size n * h` >>
  `1 <= h /\ k <= h` by rw[Abbr`h`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size c <= t` by
  (`size c <= size c * (size k ** 7 * size m * size n * h)` by rw[MULT_POS] >>
  `size c * (size k ** 7 * size m * size n * h) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size k <= t` by
    (`size k <= size k * (size c * size k ** 6 * size m * size n * h)` by rw[MULT_POS] >>
  `size k * (size c * size k ** 6 * size m * size n * h) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size m <= t` by
      (`size m <= size m * (size c * size k ** 7 * size n * h)` by rw[MULT_POS] >>
  `size m * (size c * size k ** 7 * size n * h) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size k * size n <= t` by
        (`size k * size n <= size k * size n * (size c * size k ** 6 * size m * h)` by rw[MULT_POS] >>
  `size k * size n * (size c * size k ** 6 * size m * h) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size k ** 7 * size n <= t` by
          (`k * size k ** 7 * size n <= h * size k ** 7 * size n` by rw[] >>
  `h * size k ** 7 * size n <= h * size k ** 7 * size n * (size c * size m)` by rw[MULT_POS] >>
  `h * size k ** 7 * size n * (size c * size m) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf (param_seekM m c n k) <=
            1 + 2 * size (MAX c k) + (c - k) * 36 * c * size m * size n * size c ** 8 *)
(* Proof:
   Let quit = (\k. if k = 0 then 1 else 1 + 2 * size k),
       body = (\k. size k +
                 if k = 0 then 0
                 else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                 else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                 else size k),
       cover = (\k. 36 * (MAX 1 k) * size m * size c * size n * size k ** 7),
       exit = (\k. k = 0 \/ n MOD k = 0 \/ m <= ordz k n)
       loop = (\k. stepsOf (param_seekM m c n k)).

   Then !k. loop k = if c <= k then quit k else body k + if exit k then 0 else loop (k + 1)
                                               by param_seekM_steps_by_inc_loop
    Now !x. body x <= cover x                  by param_seekM_body_bound
    and MONO cover                             by size_monotone_le
   Let z = k + bop 1 c k * 1
         = k + (c - k)                         by bop_1_m_c

   Thus loop k
     <= quit z + bop 1 c k * cover z           by loop_inc_count_cover_exit_le
   If c <= k,
      loop k = quit k
            <= 1 + 2 * size k
   Otherwise, k < c
      Then z = k + (c - k) = c.
      loop k <= quit c + (c - k) * cover c     keep (c - k).
      Note 0 < c                               by k < c
        so quit c = 1 + 2 * size c
       and cover c = 36 * (MAX 1 c) * size m * size c * size n * size c ** 7
                   = 36 * c * size m * size n * size c ** 8
   Putting all together,
      loop k <= 1 + 2 * size (MAX c k) + (c - k) * 36 * c * size m * size n * size c ** 8.
*)
val param_seekM_steps_upper = store_thm(
  "param_seekM_steps_upper",
  ``!m c n k. stepsOf (param_seekM m c n k) <=
             1 + 2 * size (MAX c k) + 36 * (c - k) * c * size m * size n * size c ** 8``,
  rpt strip_tac >>
  assume_tac param_seekM_steps_by_inc_loop >>
  last_x_assum (qspecl_then [`m`, `c`, `n`] strip_assume_tac) >>
  assume_tac param_seekM_body_bound >>
  last_x_assum (qspecl_then [`m`, `c`, `n`] strip_assume_tac) >>
  qabbrev_tac `quit = \k. if k = 0 then 1 else 1 + 2 * size k` >>
  qabbrev_tac `body = \k. size k +
                 if k = 0 then 0
                 else size c + size (c - k) + size n * size k + size (n MOD k) + if n MOD k = 0 then 0
                 else stepsOf (ordzM k n) + size (MAX m (ordz k n)) + size (m - ordz k n) + if m <= ordz k n then 0
                 else size k` >>
  qabbrev_tac `cover = \k. 36 * (MAX 1 k) * size m * size c * size n * size k ** 7` >>
  qabbrev_tac `exit = \k. (k = 0) \/ (n MOD k = 0) \/ m <= ordz k n` >>
  qabbrev_tac `loop = \k. stepsOf (param_seekM m c n k)` >>
  `loop k <= 1 + 2 * size (MAX c k) + 36 * (c - k) * c * size m * size n * size c ** 8` suffices_by rw[] >>
  `!k. loop k = if c <= k then quit k else body k + if exit k then 0 else loop (k + 1)` by metis_tac[] >>
  `0 < 1` by decide_tac >>
  `!x. body x <= cover x` by metis_tac[] >>
  `MONO cover` by
  (rw[Abbr`cover`] >>
  `size x ** 7 <= size y ** 7` by rw[size_monotone_le] >>
  `MAX 1 x <= MAX 1 y` by rw[MAX_LE] >>
  `size x ** 7 * MAX 1 x <= size y ** 7 * MAX 1 y` by rw[LE_MONO_MULT2] >>
  qabbrev_tac `p = size c * size m * size n` >>
  metis_tac[LE_MULT_LCANCEL, MULT_ASSOC]) >>
  imp_res_tac loop_inc_count_cover_exit_le >>
  first_x_assum (qspec_then `k` strip_assume_tac) >>
  qabbrev_tac `z = k + bop 1 c k * 1` >>
  Cases_on `c <= k` >| [
    `loop k = quit k` by metis_tac[] >>
    `quit k <= 1 + 2 * size k` by rw[Abbr`quit`] >>
    `size k <= size (MAX c k)` by rw[size_monotone_le] >>
    decide_tac,
    `bop 1 c k = c - k` by rw[bop_1_m_c] >>
    `z = c` by rw[Abbr`z`] >>
    `size (MAX c k) = size c` by rw[size_monotone_le, MAX_DEF] >>
    `cover z = 36 * MAX 1 c * size m * size c * size n * size c ** 7` by rw[Abbr`cover`] >>
    `MAX 1 c = c` by rw[MAX_DEF] >>
    `size c * size c ** 7 = size c ** 8` by rw[] >>
    `36 * MAX 1 c * size m * size c * size n * size c ** 7 =
    36 * MAX 1 c * size m * size n * (size c * size c ** 7)` by decide_tac >>
    `_ = 36 * c * size m * size n * size c ** 8` by rw[] >>
    `quit z <= 1 + 2 * size c` by rw[Abbr`quit`] >>
    `bop 1 c k * cover z = (c - k) * (36 * c * size m * size n * size c ** 8)` by metis_tac[] >>
    `size c <= size (MAX c k)` by rw[size_monotone_le] >>
    decide_tac
  ]);

(* Theorem: stepsOf (param_seekM m c n k) <=
            39 * (MAX 1 ((c - k) * c)) * size (MAX c k) * size m * size n * size c ** 7 *)
(* Proof:
      stepsOf (param_seekM m c n k)
   <= 1 + 2 * size (MAX c k) + 36 * (c - k) * c * size m * size n * size c ** 8
                                                    by param_seekM_steps_upper
   <= (1 + 2 + 36) * (c - k) * c * size (MAX c k) * size m * size n * size c ** 7
                                                    by dominant term
    = 39 * (c - k) * c * size (MAX c k) * size m * size n * size c ** 7
   Use (MAX 1 (c - k)) to cater for c = k,
   and (MAX 1 c) to cater for c = 0.
*)
val param_seekM_steps_bound = store_thm(
  "param_seekM_steps_bound",
  ``!m c n k. stepsOf (param_seekM m c n k) <=
             39 * (MAX 1 (c - k)) * (MAX 1 c) * size (MAX c k) * size m * size n * size c ** 7``,
  rpt strip_tac >>
  assume_tac param_seekM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `c`, `n`, `k`] strip_assume_tac) >>
  qabbrev_tac `x = MAX 1 (c - k)` >>
  qabbrev_tac `y = MAX 1 c` >>
  qabbrev_tac `z = MAX c k` >>
  qabbrev_tac `t = x * y * size z * size m * size n * size c ** 7` >>
  `stepsOf (param_seekM m c n k) <= 39 * t` suffices_by rw[Abbr`t`] >>
  `1 <= x /\ (c - k) <= x` by rw[MAX_DEF, Abbr`x`] >>
  `1 <= y /\ c <= y` by rw[Abbr`y`] >>
  `c <= z /\ k <= z` by rw[Abbr`z`] >>
  `0 < x * y` by rw[MULT_POS] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size z <= t` by
  (`size z <= size z * (x * y * size m * size n * size c ** 7)` by rw[MULT_POS] >>
  `size z * (x * y * size m * size n * size c ** 7) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `(c - k) * c * size m * size n * size c ** 8 <= t` by
    (`size c <= size z` by rw[size_monotone_le] >>
  `(c - k) * c * size c <= x * y * size z` by rw[LE_MONO_MULT2] >>
  `(c - k) * c * size m * size n * size c ** 8 = (c - k) * c * size c * (size m * size n * size c ** 7)` by rw[] >>
  `(c - k) * c * size c * (size m * size n * size c ** 7) <= x * y * size z * (size m * size n * size c ** 7)` by rw[] >>
  `x * y * size z * (size m * size n * size c ** 7) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf (paramM n) <= 19 * size n + 16904 * size n ** 2 + 1418141046 * size n ** 20 *)
(* Proof:
      stepsOf (paramM n)
    = stepsOf (ulogM n) + 2 * size (ulog n) +
      if n <= 2 then 0
      else size (ulog n) ** 2 + 2 * size (ulog n ** 5) + size (MAX (HALF (ulog n ** 5)) 2) +
           stepsOf (expM (ulog n) 5) +
           stepsOf (param_seekM (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2)  by paramM_steps_thm
   <= 2 * size (ulog n) + size (ulog n) ** 2 + 2 * size (ulog n ** 5) + size (MAX (HALF (ulog n ** 5)) 2) +
      stepsOf (ulogM n) + stepsOf (expM (ulog n) 5) +
      stepsOf (param_seekM (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2)  assume false condition

    The aim is to express each term as some power of (size n).

    Note ulog n <= size n                          by size_ulog -- this is good
     and ulog n <= n                               by ulog_le_self -- not so good
    Thus size (ulog n) <= size n                   by size_monotone_le

    Thus b = 2 * size (ulog n)
          <= 2 * size n                            for #1 term
    Thus u = size (ulog n) ** 2
          <= size n ** 2                           for #2 term

    Also size (ulog n ** 5) <= 5 * size (ulog n)   by size_exp_upper_alt
                            <= 5 * size n          by above
    Thus v = 2 * size (ulog n ** 5)
          <= 10 * size n                           for #3 term

    Note MAX (HALF (ulog n ** 5) 2)
      <= 2 + HALF (ulog n ** 5)                    by MAX_LE_SUM
     Let h = HALF (ulog n ** 5),
         c = ulog n ** 5, k = size n ** 5.
    Then h <= c                                    by HALF_LE
     and c <= k                                    by EXP_EXP_LE_MONO, ulog n <= size n
     and 0 < k                                     by EXP_POS, size_pos
      so 2 + h <= 2 + k <= 3 * k                   by h <= c, c <= k, 0 < k
     and size (2 + h) <= size (3 * k)              by size_monotone_le
                      <= size 3 + size k           by size_mult_upper
                      <= 2 + 5 * size n            by size_exp_upper_alt, above
                      <= 7 * size n                by 0 < size n

    Thus w = size (MAX (HALF (ulog n ** 5)) 2)
            <= 7 * size n                          for #4 term

     Now x = stepsOf (ulogM n)                     for #5 term
          <= 28 * size n ** 2                      by ulogM_steps_bound

     Now y = stepsOf (expM (ulog n) 5)             for #6 term
          <= 15 * MAX 1 5 ** 3 * size (ulog n) ** 2 * (size 5) ** 2    by expM_steps_bound
           = 15 * 5 ** 3 * 3 ** 2 * size (ulog n) ** 2                 by size 5 = 3
          <= 15 * (5 ** 3) * (3 ** 2) * size n ** 2
           = 16875 * size n ** 2
     Now z = stepsOf (param_seekM (SQ (ulog n)) (2 + HALF (ulog n ** 5)) n 2)  for #6 term
          <= 39 * MAX 1 h * MAX 1 (2 + h) * size (MAX (2 + h) 2) * size m * size n * size (2 + h) ** 7
                                                   by param_seekM_steps_bound, m = SQ (ulog n)
           = 39 * MAX 1 h * (2 + h) * size (2 + h) * size (SQ (ulog n)) * size n * size (2 + h) ** 7
           = 39 * MAX 1 h * (2 + h) * size (SQ (ulog n)) * size n * size (2 + h) ** 8

     Note MAX 1 h <= MAX 1 k = k                   by MAX_LE, 1 <= k, h <= k, 0 < k
      and 2 + h <= 3 * k                           by above
      and size (SQ (ulog n))
       <= size (SQ (size n))                       by size_monotone_le
       <= 2 * size (size n)                        by size_mult_upper
       <= 2 * size n                               by size_size_le
      and size (2 + h) <= 7 * size n               by above

     Thus z <= 39 * size n ** 5 * 3 * size n ** 5 * (2 * size n) * size n * (7 * size n) ** 8
             = 39 * 3 * 2 * 7 ** 8 * size n ** (5 + 5 + 1 + 1 + 8)   by EXP_ADD
             = 1348963434 * size n ** 20

    Finally,
         stepsOf (paramM n)
      <= 2 * size n + size n ** 2 + 2 * (5 * size n) + 7 * size n +
         28 * size n ** 2 + 16875 * size n ** 2 + 1348963434 * size n ** 20
       = 19 * size n + (1 + 28 + 16875) * size n ** 2 + 1348963434 * size n ** 20
       = 19 * size n + 16904 * size n ** 2 + 1348963434 * size n ** 20
*)
Theorem paramM_steps_upper:
  !n. stepsOf (paramM n) <=
      19 * size n + 16904 * size n ** 2 + 1348963434 * size n ** 20
Proof
  rpt strip_tac >>
  assume_tac paramM_steps_thm >>
  last_x_assum (qspec_then ‘n’ strip_assume_tac) >>
  qabbrev_tac ‘h = HALF (ulog n ** 5)’ >>
  qabbrev_tac ‘x = stepsOf (ulogM n)’ >>
  qabbrev_tac ‘y = stepsOf (expM (ulog n) 5)’ >>
  qabbrev_tac ‘z = stepsOf (param_seekM (SQ (ulog n)) (2 + h) n 2)’ >>
  qabbrev_tac ‘b = size (ulog n)’ >>
  qabbrev_tac ‘u = b ** 2’ >>
  qabbrev_tac ‘v = size (ulog n ** 5)’ >>
  qabbrev_tac ‘w = size (MAX h 2)’ >>
  ‘stepsOf (paramM n) <= x + 2 * b + u + 2 * v + w + y + z’ by fs[] >>
  qabbrev_tac ‘c = ulog n ** 5’ >>
  qabbrev_tac ‘k = size n ** 5’ >>
  ‘ulog n <= size n’ by rw[size_ulog] >>
  ‘ulog n <= n’ by rw[ulog_le_self] >>
  ‘b <= size n’ by rw[size_monotone_le, Abbr‘b’] >>
  ‘size c <= 5 * b’ by rw[size_exp_upper_alt, Abbr‘b’, Abbr‘c’] >>
  ‘size c <= 5 * size n’ by decide_tac >>
  ‘h <= c’ by rw[HALF_LE, Abbr‘h’] >>
  ‘c <= k’ by rw[Abbr‘c’, Abbr‘k’] >>
  ‘h <= k’ by decide_tac >>
  ‘0 < k’ by rw[Abbr‘k’] >>
  ‘2 + h <= 3 * k’ by decide_tac >>
  ‘size (2 + h) <= 7 * size n’
    by (‘size (2 + h) <= size (3 * k)’ by rw[size_monotone_le] >>
        ‘size (3 * k) <= size 3 + size k’ by rw[size_mult_upper] >>
        ‘size 3 = 2’ by EVAL_TAC >>
        ‘size k <= 5 * size (size n)’ by rw[size_exp_upper_alt, Abbr‘k’] >>
        ‘size (size n) <= size n’ by rw[size_size_le] >>
        ‘0 < size n’ by rw[] >>
        decide_tac) >>
  ‘u <= size n ** 2’ by rw[Abbr‘u’] >>
  ‘v <= 5 * size n’ by rw[Abbr‘v’] >>
  ‘w <= 7 * size n’ by
    (‘MAX h 2 <= 2 + h’ by rw[MAX_LE_SUM] >>
     ‘w <= size (2 + h)’ by rw[size_monotone_le, Abbr‘w’] >>
     decide_tac) >>
  ‘x <= 28 * size n ** 2’ by rw[ulogM_steps_bound, Abbr‘x’] >>
  ‘y <= 16875 * size n ** 2’
    by (‘y <= 15 * MAX 1 5 ** 3 * size (ulog n) ** 2 * (size 5) ** 2’
         by rw[expM_steps_bound, Abbr‘y’] >>
        ‘MAX 1 5 = 5’ by rw[] >>
        ‘size 5 = 3’ by EVAL_TAC >>
        ‘15 * MAX 1 5 ** 3 * size (ulog n) ** 2 * (size 5) ** 2 =
         15 * 125 * 9 * size (ulog n) ** 2’ by rw[] >>
        ‘size (ulog n) ** 2 <= size n ** 2’ by rw[] >>
        decide_tac) >>
  ‘z <= 1348963434 * size n ** 20’
    by (‘z <= 39 * MAX 1 (2 + h - 2) * (MAX 1 (2 + h)) * size (MAX (2 + h) 2) *
              size (SQ (ulog n)) * size n * size (2 + h) ** 7’
         by rw[param_seekM_steps_bound, Abbr‘z’, Abbr‘h’] >>
        ‘2 + h - 2 = h’ by decide_tac >>
        ‘MAX 1 h <= MAX 1 k’ by rw[] >>
        ‘MAX 1 k = k’
          by (rw[MAX_DEF, Abbr‘k’] >> ‘size n ≤ 1’ by simp[] >>
              ‘size n ≠ 0’ by (strip_tac >> fs[]) >> simp[]) >>
        ‘MAX 1 (2 + h - 2) <= size n ** 5’ by metis_tac[] >>
        ‘MAX 1 (2 + h) = 2 + h’ by rw[MAX_DEF] >>
        ‘MAX 1 (2 + h) <= 3 * size n ** 5’ by metis_tac[] >>
        ‘size (MAX (2 + h) 2) = size (2 + h)’ by rw[MAX_DEF] >>
        ‘size (MAX (2 + h) 2) <= 7 * size n’ by decide_tac >>
        ‘size (SQ (ulog n)) <= size (size n ** 2)’ by rw[size_monotone_le] >>
        ‘size (size n ** 2) <= 2 * size (size n)’ by rw[size_exp_upper_alt] >>
        ‘size (size n) <= size n’ by rw[size_size_le] >>
        ‘size (SQ (ulog n)) <= 2 * size n’ by decide_tac >>
        ‘size (2 + h) ** 7 <= (7 * size n) ** 7’ by rw[] >>
        ‘(7 * size n) ** 7 = 7 ** 7 * size n ** 7’ by rw[EXP_BASE_MULT] >>
        ‘size (2 + h) ** 7 <= 7 ** 7 * size n ** 7’ by decide_tac >>
        ‘39 * MAX 1 (2 + h - 2) * MAX 1 (2 + h) * size (MAX (2 + h) 2) * size (SQ (ulog n)) * size n * size (2 + h) ** 7 <=
         39 * size n ** 5 * (3 * size n ** 5) * (7 * size n) * (2 * size n) * size n * (7 ** 7 * size n ** 7)’ by rw[LE_MONO_MULT2] >>
        ‘z <= 39 * 3 * 7 * 2 * 7 ** 7 * (size n ** 5 * size n ** 5 * size n * size n * size n * size n ** 7)’ by decide_tac >>
        ‘SQ (size n ** 5) * size n * size n * size n * size n ** 7 =
         SQ (size n ** 5) * size n ** 1 * size n ** 1 * size n ** 1 * size n ** 7’ by rw[] >>
        ‘_ = size n ** 20’ by rw[] >>
        ‘39 * 3 * 7 * 2 * 7 ** 7 = 1348963434’ by EVAL_TAC >>
        metis_tac[]) >>
  decide_tac
QED

(* Theorem: stepsOf (paramM n) <= 1348980357 * size n ** 20 *)
(* Proof:
      stepsOf (paramM n)
   <= 19 * size n + 16904 * size n ** 2 + 1348963434 * size n ** 20   by paramM_steps_upper
   <= (19 + 16904 + 1348963434) * size n ** 20                        by dominant term
    = 1348980357 * size n ** 20
*)
val paramM_steps_bound = store_thm(
  "paramM_steps_bound",
  ``!n. stepsOf (paramM n) <= 1348980357 * size n ** 20``,
  rpt strip_tac >>
  assume_tac paramM_steps_upper >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  `size n ** 1 <= size n ** 20` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `size n ** 2 <= size n ** 20` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  `size n = size n ** 1` by rw[] >>
  decide_tac);

(* Theorem: (stepsOf o paramM) IN O_poly 20 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (paramM n) <= k * size n ** 20
   Note stepsOf (paramM n) <= 1348980357 * size n ** 17   by paramM_steps_bound
   Take any h, but use k = 1348980357, the result follows.
*)
val paramM_steps_O_poly = store_thm(
  "paramM_steps_O_poly",
  ``(stepsOf o paramM) IN O_poly 20``,
  rw[O_poly_thm] >>
  metis_tac[paramM_steps_bound]);

(* This is a milestone result! *)

(* Theorem: (stepsOf o paramM) IN big_O (\n. (ulog n) ** 20) *)
(* Proof:
   Note (stepsOf o paramM) IN O_poly 20    by paramM_steps_O_poly
    and O_poly 20
      = big_O (POLY 20 o ulog)             by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 20)                 by POLY_def, FUN_EQ_THM
   The result follows.
*)
val paramM_steps_big_O = store_thm(
  "paramM_steps_big_O",
  ``(stepsOf o paramM) IN big_O (\n. (ulog n) ** 20)``,
  assume_tac paramM_steps_O_poly >>
  `O_poly 20 = big_O (POLY 20 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 20 o ulog = \n. (ulog n) ** 20` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (paramM n) = param n) /\
       (stepsOf o paramM) IN big_O (\n. (ulog n) ** 20) *)
(* Proof: by paramM_value, paramM_steps_big_ *)
val paramM_thm = store_thm(
  "paramM_thm",
  ``!n. (valueOf (paramM n) = param n) /\
       (stepsOf o paramM) IN big_O (\n. (ulog n) ** 20)``,
  metis_tac[paramM_value, paramM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
