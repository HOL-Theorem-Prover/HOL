(* ------------------------------------------------------------------------- *)
(* Order Computations with Count Monad                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countOrder";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory logrootTheory pairTheory optionTheory
     listRangeTheory;

open countMonadTheory countMacroTheory;
open countModuloTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;

open computeOrderTheory; (* for ordz_seek and ordz_simple *)
open ringInstancesTheory; (* for ZN_order_mod_1, ZN_order_mod *)

(* (* val _ = load "monadsyntax"; *) *)
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Order Computations with Count Monad Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Multiplicative Order Computation:
   ordz_seekM_def    |- !n m j c. ordz_seekM m n c j =
                                  do
                                    m0 <- zeroM m;
                                    if m0 then 0c
                                    else
                                      do
                                        b0 <- leqM c j;
                                        if b0 then 0c
                                        else
                                          do
                                            x <- mexpM m n j;
                                            x1 <- oneM x;
                                            if x1 then unit j
                                            else do k <- incM j; ordz_seekM m n c k od
                                          od
                                      od
                                  od
   ordzM_def         |- !m n. ordzM m n =
                              do
                                m0 <- zeroM m;
                                m1 <- oneM m;
                                if m0 then unit (ordz 0 n)
                                else if m1 then 1c
                                else do n' <- modM n m; ordz_seekM m n' m 1 od
                              od
#  ordz_seekM_value  |- !m n c j. 0 < m ==> valueOf (ordz_seekM m n c j) = ordz_seek m n c j
#  ordzM_value       |- !m n. valueOf (ordzM m n) = ordz m n

   ordz_seekM_steps_thm
                     |- !m n c j. stepsOf (ordz_seekM m n c j) =
                                  size (MAX c j) + size (c - j) +
                                  if c <= j then 0
                                  else stepsOf (mexpM m n j) + size (n ** j MOD m) +
                                       if n ** j MOD m = 1 then 0
                                       else size j + stepsOf (ordz_seekM m n c (j + 1))
   ordz_seekM_steps_base
                     |- !m n c. 1 < m ==> stepsOf (ordz_seekM m n c 0) =
                                if c = 0 then 2 else 2 + TWICE (size c) + TWICE (size m)
   ordzM_steps_thm   |- !m n. stepsOf (ordzM m n) = TWICE (size m) + if m <= 1 then 0
                              else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)
   ordz_seekM_steps_by_inc_loop
                     |- !m n c. (let body j = size c + size (c - j) +
                                              stepsOf (mexpM m n j) +
                                              size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
                                  in 0 < m ==>
                                     !j. stepsOf (ordz_seekM m n c j) =
                                         if c <= j then 1 + size j
                                         else body j +
                                              if n ** j MOD m = 1 then 0
                                              else stepsOf (ordz_seekM m n c (j + 1)))
   ordz_seekM_body_upper
                     |- !m n c. (let body j =
                                     size c + size (c - j) + stepsOf (mexpM m n j) +
                                     size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
                                  in 0 < m ==>
                                     !j. body j <= size j + size m + TWICE (size c) +
                                                  17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2)
   ordz_seekM_body_bound
                     |- !m n c. (let body j = if m = 0 then 1
                                       else size m + size c + size (c - j) + stepsOf (mexpM m n j) +
                                       size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
                                  in 0 < m ==>
                                     !j. body j <= 22 * size c * size j ** 2 *
                                                   size m ** 2 * size (MAX n m) ** 2)
   ordz_seekM_steps_upper
                     |- !m n c j. 0 < m ==> stepsOf (ordz_seekM m n c j) <=
                                  1 + size (MAX j c) +
                                  22 * c * size c ** 3 * size m ** 2 * size (MAX n m) ** 2
   ordz_seekM_steps_bound
                     |- !m n c j. 0 < m ==> stepsOf (ordz_seekM m n c j) <=
                                        24 * MAX 1 c * size (MAX j c) * size m ** 2 *
                                             size (MAX n m) ** 2 * size c ** 3
   ordzM_steps_upper       |- !m n. stepsOf (ordzM m n) <=
                                    1 + 3 * size m + size n * size m + 22 * m * size m ** 7
   ordzM_steps_bound       |- !m n. stepsOf (ordzM m n) <= 27 * MAX 1 m * size n * size m ** 7
   ordzM_steps_O_poly      |- !m. stepsOf o ordzM m IN O_poly 1
   ordzM_steps_big_O       |- !m. stepsOf o ordzM m IN big_O (\n. ulog n)
   ordzM_steps_O_swap      |- !n. stepsOf o combin$C ordzM n IN
                                  big_O (POLY 1 o (\m. MAX 1 m * size m ** 7))
   ordzM_thm               |- !m n. (valueOf (ordzM m n) = ordz m n) /\
                                    stepsOf o ordzM m IN big_O (\n. ulog n)

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
(* Multiplicative Order Search                                               *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:
Input: m, n.       m = modulus.
Output: ordz m n, the least index j such that (n ** j = 1) (mod m)

ordz_seek:
   if m = 0, return 0     // since (mod 0) is undefined
   loop:
      if j = m, return 0  // exit
      if (n ** j) mod m = 1 return j     // found j satisfying the condition
      j <- j + 1          // increment j
      goto loop           // go back

To compute the ordz m n:
    if n = 0 then ordz m 0         // undefined for n = 0
    else if m = 0 then ordz 0 n    // undefined for m = 0
    else if m = 1 then 1           // ordz 1 n = 1   by ZN_order_mod_1
    else ordz_seek m n m 1         // ordz_seek m n m 1 = ordz m n  by ordz_seek_eq_order, 1 < m
*)

(* ------------------------------------------------------------------------- *)
(* Multiplicative Order Computation                                          *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode:
   Given modulo m, a number n, and a cutoff c,
   starting with j = c - 1, find the least k such that n ** k MOD m = 1.
   if m = 0, return 0
   loop:
      if j = 0, return 0
      k <- c - j   // k = 1, 2, 3, ...., up to c
      x <- n ** k MOD m
      if x = 1 then return k
      j <- j - 1
   goto loop

   To compute ordz m n:
      if m = 0 then return ordz 0 n   // undefined
      else if m = 1 then return 1     // ordz 1 n = 1  by ZN_order_mod_1
      else call this search with c = m, j = c.      // by ordz_seek_thm
*)

(*
> ordz_seek_def;
val it = |- !n m j c.
          ordz_seek m n c j =
          if c <= j then 0
          else if n ** j MOD m = 1 then j
          else ordz_seek m n c (SUC j): thm
*)

(* Search for least index *)
Definition ordz_seekM_def:
  ordz_seekM m n c j =
      do
         b0 <- leqM c j;
         if b0 then return 0
         else do
                x <- mexpM m n j;
                x1 <- oneM x;
                if x1 then return j
                else do
                       k <- incM j;
                       ordz_seekM m n c k;
                     od
              od
      od
Termination WF_REL_TAC `measure (λ(m,n,c,j). c - j)` >> simp[]
End

(*
> EVAL ``MAP (\n. ordz_seekM 7 n 7 1) [1 .. 6]``;  =
      [(1,Count 34); (3,Count 255); (6,Count 664); (3,Count 262); (6,Count 745); (2,Count 146)]: thm
> EVAL ``MAP (ordz 7) [1 .. 6]``; = [1; 3; 6; 3; 6; 2]: thm

> EVAL ``MAP (\n. ordz_seekM 6 n 6 1) [1 .. 6]``; =
      [(1,Count 34); (0,Count 561); (0,Count 506); (0,Count 635); (2,Count 140); (0,Count 452)]: thm
> EVAL ``MAP (ordz 6) [1 .. 6]``; = [1; 0; 0; 0; 2; 0]: thm
*)

(*
> ordz_seek_thm;
val it = |- !m n. 1 < m ==> ordz_seek m n m 1 = ordz m n: thm

when m = 0, ordz 0 n is undefined.
when m = 1, ordz 1 n = 1 by ZN_order_mod_1, but ordz_seek 1 n c j = 0 by ordz_seek_1_n.
when m <> 1, ordz m 0 = 0 by ZN_order_0, and ordz_seek m 0 c j = 0 by ordz_seek_m_0.
*)

(*
> ordz_compute_def;
val it = |- !m n.
          ordz_compute m n =
          if m = 0 then ordz 0 n else if m = 1 then 1 else ordz_seek m n m 1: thm
*)

(* Compute ordz m n *)
(* version without n MOD m:
val ordzM_def = Define`
    ordzM m n =
       do
          m0 <- zeroM m;
          m1 <- oneM m;
          if m0 then return (ordz 0 n)
          else if m1 then return 1
          else ordz_seekM m n m 1;
       od
`;
*)
(* Version with n MOD m, better for complexity analysis. *)
val ordzM_def = Define`
    ordzM m n =
       do
          m0 <- zeroM m;
          m1 <- oneM m;
          if m0 then return (ordz 0 n)
          else if m1 then return 1
          else do
                 n' <- modM n m; (* reduce n to (n MOD m) *)
                 ordz_seekM m n' m 1;
               od
       od
`;

(*
> EVAL ``MAP (ordzM 7) [1 .. 10]``; =
        [(1,Count 46); (3,Count 276); (6,Count 694); (3,Count 286); (6,Count 778);
         (2,Count 167); (0,Count 449); (1,Count 55); (3,Count 282); (6,Count 700)]: thm
-- compare with old version when no reduction to (n MOD m):
        [(1,Count 43); (3,Count 270); (6,Count 688); (3,Count 277); (6,Count 769);
         (2,Count 158); (0,Count 590); (1,Count 88); (3,Count 362); (6,Count 844)]: thm
-- since n is fixed in ordz_seekM, (n MOD m) runs eventually faster.
> EVAL ``MAP (ordz 7) [1 .. 10]``;  = [1; 3; 6; 3; 6; 2; 0; 1; 3; 6]: thm
*)

(* Theorem: 0 < m ==> (valueOf (ordz_seekM m n c j) = ordz_seek m n c j) *)
(* Proof:
   By induction from ordz_seekM_def, this is to show:
   (1) c <= j ==> 0 = ordz_seek m n c j, true   by ordz_seek_over
   (2) 0 < m /\ ~(c <= j) ==>
       valueOf (if n ** j MOD m = 1 then unit j
                else do k <- incM j; ordz_seekM m n c k od) = ordz_seek m n c j
       If n ** j MOD m = 1, to show:
          j = ordz_seek m n c j, true           by ordz_seek_exit
       If n ** j MOD m <> 1, to show:
          valueOf (ordz_seekM m n c (j + 1)) = ordz_seek m n c j
          valueOf (ordz_seekM m n c (j + 1))
        = ordz_seek m n c (j + 1)               by induction hypothesis
        = ordz_seek m n c (SUC j)               by ADD1
        = ordz_seek m n c j                     by ordz_seek_next
*)
val ordz_seekM_value = store_thm(
  "ordz_seekM_value[simp]",
  ``!m n c j. 0 < m ==> (valueOf (ordz_seekM m n c j) = ordz_seek m n c j)``,
  ho_match_mp_tac (theorem "ordz_seekM_ind") >>
  (rw[] >> rw[Once ordz_seekM_def]) >-
  simp[ordz_seek_over] >>
  `j < c` by decide_tac >>
  (Cases_on `n ** j MOD m = 1` >> simp[]) >-
  metis_tac[ordz_seek_exit] >>
  metis_tac[ordz_seek_next, ADD1]);

(* Theorem: valueOf (ordzM m n) = ordz m n *)
(* Proof:
     valueOf (ordzM m n)
   = if (m = 0) then (ordz 0 n)
     else if (m = 1) then 1
     else valueOf (ordz_seekM m (n MOD m) m 1)   by ordzM_def
   = if (m = 0) then (ordz 0 n)
     else if (m = 1) then (ordz 1 n)             by ZN_order_mod_1
     else ordz_seek m (n MOD m) m 1              by ordz_seekM_value
   = if (m = 0) then (ordz 0 n)
     else if (m = 1) then (ordz 1 n)
     else ordz m (n MOD m)                       by ordz_seek_thm, 1 < m
   = if (m = 0) then (ordz 0 n)
     else if (m = 1) then (ordz 1 n)
     else ordz m n                               by ZN_order_mod, 0 < m
*)
val ordzM_value = store_thm(
  "ordzM_value[simp]",
  ``!m n. valueOf (ordzM m n) = ordz m n``,
  rw[ordzM_def] >-
  rw[ZN_order_mod_1] >>
  rw[ordz_seek_thm, ZN_order_mod]);

(* ------------------------------------------------------------------------- *)

(* Theorem: stepsOf (ordz_seekM m n c j) =
            size (MAX c j) + size (c - j) + if c <= j then 0
            else stepsOf (mexpM m n j) + size (n ** j MOD m) +
                 if (n ** j MOD m = 1) then 0 else size j + stepsOf (ordz_seekM m n c (j + 1)) *)
(* Proof:
     stepsOf (ordz_seekM m n c j)
   = stepsOf (leqM c j) + if c <= j then 0
          else stepsOf (mexpM m n j) +
               stepsOf (oneM (n ** j MOD m)) + if (n ** j MOD m = 1) then 0
          else stepsOf (incM j) +
               stepsOf (ordz_seekM m n c (j + 1))    by ordz_seekM_def
   = size (MAX c j) + size (c - j) + if c <= j then 0     by size_max
     else stepsOf (mexpM m n j) + size (n ** j MOD m) +
          if (n ** j MOD m = 1) then 0 else size j + stepsOf (ordz_seekM m n c (j + 1))
*)
val ordz_seekM_steps_thm = store_thm(
  "ordz_seekM_steps_thm",
  ``!m n c j. stepsOf (ordz_seekM m n c j) =
     size (MAX c j) + size (c - j) + if c <= j then 0
     else stepsOf (mexpM m n j) + size (n ** j MOD m) +
          if (n ** j MOD m = 1) then 0 else size j + stepsOf (ordz_seekM m n c (j + 1))``,
  rw[Once ordz_seekM_def, size_max]);

(* Theorem: 1 < m ==>
            (stepsOf (ordz_seekM m n c 0) =
                if c = 0 then 2 else 2 + 2 * size c + 2 * size m) *)
(* Proof:
   Note if 1 < m, n ** 0 MOD m = 1     by EXP_0, ONE_MOD
       stepsOf (ordz_seekM m n c 0)
     = size (MAX c 0) + size (c - 0) + if c <= 0 then 0
       else stepsOf (mexpM m n 0) + size (n ** 0 MOD m) + 0
                                       by ordz_seekM_steps_thm
     If c = 0, this is
     = size (MAX 0 0) + size (0 - 0) = 2   by size_0
     If c <> 0, this is
     = size c + size c + stepsOf (mexpM m n 0) + size 1   by MAX_DEF, 0 < c
     = 2 * size c + (1 + 2 * size m) + 1                  by mexpM_steps_base
     = 2 + 2 * size c + 2 * size m
*)
val ordz_seekM_steps_base = store_thm(
  "ordz_seekM_steps_base",
  ``!m n c. 1 < m ==>
           (stepsOf (ordz_seekM m n c 0) =
               if c = 0 then 2 else 2 + 2 * size c + 2 * size m)``,
  rpt strip_tac >>
  (Cases_on `c = 0` >> simp[]) >-
  rw[Once ordz_seekM_steps_thm] >>
  `MAX c 0 = c` by rw[] >>
  `n ** 0 MOD m = 1` by rw[EXP_0, ONE_MOD] >>
  rw[Once ordz_seekM_steps_thm, mexpM_steps_base]);

(* Theorem: stepsOf (ordzM m n) =
            2 * size m + if m <= 1 then 0 else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1) *)
(* Proof:
     stepsOf (ordzM m n)
   = stepsOf (zeroM m) +
     stepsOf (oneM m) +
     if m = 0 then 0 else if m = 1 then 0
     else stepsOf (modM n m) + stepsOf (ordz_seekM m (n MOD m) m 1)   by ordzM_def
   = size m + size m + if m = 0 \/ m = 1 then 0
     else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)
   = 2 * size m + if m <= 1 then 0 else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)
*)
val ordzM_steps_thm = store_thm(
  "ordzM_steps_thm",
  ``!m n. stepsOf (ordzM m n) =
         2 * size m + if m <= 1 then 0 else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)``,
  rw[ordzM_def]);

(* Theorem: let body j = size c + size (c - j) +
                stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
             in 0 < m ==>
               !j. stepsOf (ordz_seekM m n c j) =
                   if c <= j then (1 + size j) else body j +
                   if (n ** j MOD m = 1) then 0 else stepsOf (ordz_seekM m n c (j + 1)) *)
(* Proof:
     stepsOf (ordz_seekM m n c j)
   = size (MAX c j) + size (c - j) + if c <= j then 0
     else stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0
     else size j + stepsOf (ordz_seekM m n c (j + 1))    by ordz_seekM_steps_thm
   = if c <= j then (size (MAX c j) + size (c - j))
     else (size (MAX c j) + size (c - j) +
           stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j)
      + if (n ** j MOD m = 1) then 0 else stepsOf (ordz_seekM m n c (j + 1))
   = if c <= j then (size j + size 0)    by MAX_DEF
     else (size c + size (c - j) +       by MAX_DEF
           stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j)
      + if (n ** j MOD m = 1) then 0 else stepsOf (ordz_seekM m n c (j + 1))
   = if c <= j then (1 + size j)
     else (size c + size (c - j) +
           stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j)
      + if (n ** j MOD m = 1) then 0 else stepsOf (ordz_seekM m n c (j + 1))
*)
val ordz_seekM_steps_by_inc_loop = store_thm(
  "ordz_seekM_steps_by_inc_loop",
  ``!m n c. let body j = size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
            in 0 < m ==>
               !j. stepsOf (ordz_seekM m n c j) =
                   if c <= j then (1 + size j) else body j +
                   if (n ** j MOD m = 1) then 0 else stepsOf (ordz_seekM m n c (j + 1))``,
  rw[Once ordz_seekM_steps_thm] >>
  (Cases_on `c <= j` >> simp[]) >| [
    `MAX c j = j` by rw[MAX_DEF] >>
    `c - j = 0` by decide_tac >>
    simp[],
    `MAX c j = c` by rw[MAX_DEF] >>
    simp[]
  ]);

(*
This puts ordz_seekM_steps in the category: increasing loop with body cover and exit.
   ordz_seekM_steps_by_inc_loop:
        !j. loop j = if c <= j then quit j else body j + if exit j then 0 else loop (j + 1)
suitable for: loop_inc_count_cover_exit_le
*)

(* First, work out a cover for the complex body. *)

(* Theorem: let body j = size c + size (c - j) +
                stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
            in 0 < m ==>
               !j. body j <= size j + size m + 2 * size c +
                             17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2 *)
(* Proof:
   Let eq = (\j. n ** j MOD m = 1).
     body j
   = size c + size (c - j) +
        stepsOf (mexpM m n j) + size (n ** j MOD m) + if eq j then 0 else size j
  <= size c + size (c - j) + stepsOf (mexpM m n j) + size (n ** j MOD m) + size j
  <= size c + size (c - j) + (17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2) +
     size k + size j                                 by mexpM_steps_bound
     where k = n ** j MOD m.
     Note c - j <= c, so size (c - j) <= size c      by size_monotone_le
      and k < m, so size k <= size m                 by MOD_LESS, 0 < m, size_monotone_lt
  <= sc + sc + 17 * sj ** 2 * sm ** 2 * size (MAX n m) ** 2 + sm + sj
   = sj + sm + 2 * sc + 17 * sj ** 2 * sm ** 2 * size (MAX n m) ** 2
*)
val ordz_seekM_body_upper = store_thm(
  "ordz_seekM_body_upper",
  ``!m n c. let body j = size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
            in 0 < m ==>
               !j. body j <= size j + size m + 2 * size c +
                             17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2``,
  rw_tac std_ss[] >>
  `body j <= size j + size c + size (c - j) + size (n ** j MOD m) + stepsOf (mexpM m n j)` by rw[Abbr`body`] >>
  qabbrev_tac `k = n ** j MOD m` >>
  `k < m` by rw[MOD_LESS, Abbr`k`] >>
  `size k <= size m` by rw[size_monotone_lt] >>
  `size (c - j) <= size c` by rw[size_monotone_le] >>
  `stepsOf (mexpM m n j) <= 17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2` by rw[mexpM_steps_bound] >>
  decide_tac);

(* Theorem: let body j = size c + size (c - j) +
                stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
             in 0 < m ==>
                !j. body j <= 22 * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2 *)
(* Proof:
      body j
   <= size j + size m + 2 * size c + 17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2
                                                                 by ordz_seekM_body_upper
   <= (1 + 1 + 2 + 1 + 17) * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2
                                                                 by dominant term
    = 22 * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2
*)
val ordz_seekM_body_bound = store_thm(
  "ordz_seekM_body_bound",
  ``!m n c. let body j = size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j
            in 0 < m ==>
               !j. body j <= 22 * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2``,
  rpt strip_tac >>
  assume_tac ordz_seekM_body_upper >>
  last_x_assum (qspecl_then [`m`, `n`, `c`] strip_assume_tac) >>
  qabbrev_tac `eq = \j. n ** j MOD m = 1` >>
  qabbrev_tac `body = \j. size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if eq j then 0 else size j` >>
  `!j. 0 < m ==> body j <= 22 * size c * size j ** 2 * size m ** 2 * size (MAX n m) ** 2` suffices_by fs[] >>
  rpt strip_tac >>
  `body j <= size j + size m + TWICE (size c) + 17 * size j ** 2 * size m ** 2 * size (MAX n m) ** 2` by fs[] >>
  qabbrev_tac `sc = size c` >>
  qabbrev_tac `sj = size j` >>
  qabbrev_tac `sm = size m` >>
  qabbrev_tac `sn = size (MAX n m)` >>
  qabbrev_tac `t = sc * sj ** 2 * sm ** 2 * sn ** 2` >>
  `body j <= 22 * t` suffices_by rw[] >>
  `0 < t` by rw[MULT_POS, Abbr`sc`, Abbr`sj`, Abbr`sm`, Abbr`sn`, Abbr`t`] >>
  `sj <= t` by
  (`sj <= sj * (sc * sj * sm ** 2 * sn ** 2)` by rw[MULT_POS, Abbr`sc`, Abbr`sj`, Abbr`sm`, Abbr`sn`] >>
  `sj * (sc * sj * sm ** 2 * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sm <= t` by
    (`sm  <= sm * (sc * sj ** 2 * sm * sn ** 2)` by rw[MULT_POS, Abbr`sc`, Abbr`sj`, Abbr`sm`, Abbr`sn`] >>
  `sm * (sc * sj ** 2 * sm * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sc <= t` by
      (`sc <= sc * (sj ** 2 * sm ** 2 * sn ** 2)` by rw[MULT_POS, Abbr`sj`, Abbr`sm`, Abbr`sn`] >>
  `sc * (sj ** 2 * sm ** 2 * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sj ** 2 * sm ** 2 * sn ** 2 <= t` by
        (`sj ** 2 * sm ** 2 * sn ** 2 <= sj ** 2 * sm ** 2 * sn ** 2 * sc` by rw[MULT_POS, Abbr`sc`] >>
  `sj ** 2 * sm ** 2 * sn ** 2 * sc = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: 0 < m ==> stepsOf (ordz_seekM m n c j) <=
            1 + size (MAX j c) + 22 * c * (size c) ** 3 * size m ** 2 * size (MAX n m) ** 2 *)
(* Proof:
   Let eq = (\j. n ** j MOD m = 1)
       body = (\j. size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if eq j then 0 else size j),
       cover = (\j. 22 * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2),
       quit = (\j. 1 + size j),
       exit = (\j. eq j)
       loop = (\j. stepsOf (ordz_seekM m n c j)).

   Then !j. loop j = if c <= j then quit j else body j + if exit j then 0 else loop (j + 1)
                                               by ordz_seekM_steps_by_inc_loop
    Now !x. body x <= cover x                  by ordz_seekM_body_bound
    and MONO cover                             by size_monotone_le
   Let n = bop 1 c j = c - j                   by bop_1_m_c
       z = j + (bop 1 c j) * 1 = j + (c - j)   by bop_1_m_c

   Thus loop j
     <= quit z + n * cover z                   by loop_inc_count_cover_exit_le
      = quit z + (c - j) * cover z             by above

   If c <= j,
       Then n = 0, z = j.
        loop j <= quit j + 0                   In fact, loop j = quit j by given
                = 1 + size j
   Otherwise, j < c.
       Then n = c - j <= c
        and z = c
   Thus loop j
     <= quit c + c * cover c         by (c - j) < c
     <= 1 + size c + c * 22 * size c * (size c) ** 2 * size m ** 2 * size (MAX n m) ** 2
     <= 1 + size c + 22 * c * (size c) ** 3 * size m ** 2 * size (MAX n m) ** 2
   To cater for both cases, replace + size c by + size (MAX j c).
*)
val ordz_seekM_steps_upper = store_thm(
  "ordz_seekM_steps_upper",
  ``!m n c j. 0 < m ==> stepsOf (ordz_seekM m n c j) <=
             1 + size (MAX j c) + 22 * c * (size c) ** 3 * size m ** 2 * size (MAX n m) ** 2``,
  rpt strip_tac >>
  assume_tac ordz_seekM_steps_by_inc_loop >>
  first_x_assum (qspecl_then [`m`, `n`, `c`] strip_assume_tac) >>
  assume_tac ordz_seekM_body_bound >>
  first_x_assum (qspecl_then [`m`, `n`, `c`] strip_assume_tac) >>
  qabbrev_tac `body = \j. size c + size (c - j) +
               stepsOf (mexpM m n j) + size (n ** j MOD m) + if n ** j MOD m = 1 then 0 else size j` >>
  qabbrev_tac `cover = \j. 22 * size c * (size j) ** 2 * size m ** 2 * size (MAX n m) ** 2` >>
  qabbrev_tac `exit = \j. n ** j MOD m = 1` >>
  qabbrev_tac `quit = \j. 1 + size j` >>
  qabbrev_tac `loop = \j. stepsOf (ordz_seekM m n c j)` >>
  `loop j <= quit (MAX j c) + 22 * c * size c ** 3 * size m ** 2 * size (MAX n m) ** 2` suffices_by rw[Abbr`loop`, Abbr`quit`] >>
  `!j. loop j = if c <= j then quit j else body j + if exit j then 0 else loop (j + 1)` by metis_tac[] >>
  `!j. body j <= cover j` by metis_tac[] >>
  `MONO cover` by rw[size_monotone_le, Abbr`cover`] >>
  `0 < 1` by decide_tac >>
  assume_tac loop_inc_count_cover_exit_le >>
  first_x_assum (qspecl_then [`loop`, `body`, `quit`, `cover`, `exit`, `1`, `c`] strip_assume_tac) >>
  qabbrev_tac `foo = !j. loop j = if c <= j then quit j else body j + if exit j then 0 else loop (j + 1)` >>
  fs[bop_1_m_c] >>
  `loop j <= quit (j + (c - j)) + cover (j + (c - j)) * (c - j)` by fs[] >>
  Cases_on `c <= j` >| [
    `c - j = 0` by decide_tac >>
    `quit (j + (c - j)) + cover (j + (c - j)) * (c - j) = quit j` by rw[] >>
    `quit j <= quit (MAX j c)` by rw[size_monotone_le, Abbr`quit`] >>
    decide_tac,
    `j < c` by decide_tac >>
    `quit (j + (c - j)) + cover (j + (c - j)) * (c - j) = quit c + (c - j) * cover c` by rw[] >>
    `quit c <= quit (MAX j c)` by rw[size_monotone_le, Abbr`quit`] >>
    `(c - j) * cover c <= c * cover c` by rw[] >>
    `loop j <= quit (MAX j c) + c * cover c` by decide_tac >>
    `c * cover c = 22 * (c * size c ** 3 * size m ** 2 * size (MAX n m) ** 2)` by rw[Abbr`cover`] >>
    decide_tac
  ]);

(* Theorem: 0 < m ==> stepsOf (ordz_seekM m n c j) <=
            24 * (MAX 1 c) * size (MAX j c) * size m ** 2 * size (MAX n m) ** 2 * size c ** 3 *)
(* Proof:
      stepsOf (ordz_seekM m n c j)
   <= 1 + size (MAX j c) + 22 * c * size c ** 3 * size m ** 2 * size (MAX n m) ** 2
                                                        by ordz_seekM_steps_upper
   <= (1 + 1 + 22) * c * size (MAX j c) * size m ** 2 * size (MAX n m) ** 2 * size c ** 3
                                                        by dominant term
    = 24 * c * size (MAX j c) * size m ** 2 * size (MAX n m) ** 2 * size c ** 3
   Use (MAX 1 c) to cater for c = 0.
*)
val ordz_seekM_steps_bound = store_thm(
  "ordz_seekM_steps_bound",
  ``!m n c j. 0 > m ==> stepsOf (ordz_seekM m n c j) <=
             24 * (MAX 1 c) * size (MAX j c) * size m ** 2 * size (MAX n m) ** 2 * size c ** 3``,
  rpt strip_tac >>
  assume_tac ordz_seekM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `n`, `c`, `j`] strip_assume_tac) >>
  qabbrev_tac `m1 = MAX 1 c` >>
  qabbrev_tac `m2 = MAX j c` >>
  qabbrev_tac `m3 = MAX n m` >>
  qabbrev_tac `t = m1 * size m2 * size m ** 2 * size m3 ** 2 * size c ** 3` >>
  `stepsOf (ordz_seekM m n c j) <= 24 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m1 /\ c <= m1` by rw[Abbr`m1`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size m <= t` by
  (`size m <= size m * (m1 * size m2 * size m * size m3 ** 2 * size c ** 3)` by rw[MULT_POS] >>
  `size m * (m1 * size m2 * size m * size m3 ** 2 * size c ** 3) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size m2 <= t` by
    (`size m2 <= size m2 * (m1 * size m ** 2 * size m3 ** 2 * size c ** 3)` by rw[MULT_POS] >>
  `size m2 * (m1 * size m ** 2 * size m3 ** 2 * size c ** 3) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `c * size c ** 3 * size m ** 2 * size m3 ** 2 <= t` by
      (`c * size c ** 3 * size m ** 2 * size m3 ** 2 <= m1 * size c ** 3 * size m ** 2 * size m3 ** 2` by rw[] >>
  `m1 * size c ** 3 * size m ** 2 * size m3 ** 2 <= m1 * size c ** 3 * size m ** 2 * size m3 ** 2 * size m2` by rw[MULT_POS] >>
  `m1 * size c ** 3 * size m ** 2 * size m3 ** 2 * size m2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf (ordzM m n) <= 1 + 3 * size m + size n * size m + 22 * m * (size m) ** 7 *)
(* Proof:
      stepsOf (ordzM m n)
    = 2 * size m + if m <= 1 then 0 else size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)
                                                          by ordzM_steps_thm
   If m <= 1, this is trivial, as there is 4 * size m on RHS.
   Otherwise,
   <= 2 * size m + size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)
   <= 2 * size m + size n * size m +
      1 + size (MAX 1 m) + 22 * m * size m ** 3 * size m ** 2 * size (MAX (n MOD m) m) ** 2
                                                          by ordz_seekM_steps_upper
    = 2 * size m + size n * size m +
      1 + size m + 22 * m * size m ** 3 * size m ** 2 * size m ** 2
                                                          by MAX_IDEM, MOD_LESS: n MOD m < m, 0 < m.
    = 1 + 3 * size m + size n * size m + 22 * m * (size m) ** 7
                                                          by EXP_BASE_MULT, EXP_EXP_MULT
*)
val ordzM_steps_upper = store_thm(
  "ordzM_steps_upper",
  ``!m n. stepsOf (ordzM m n) <= 1 + 3 * size m + size n * size m + 22 * m * (size m) ** 7``,
  rpt strip_tac >>
  assume_tac ordzM_steps_thm >>
  last_x_assum (qspecl_then [`m`, `n`] strip_assume_tac) >>
  Cases_on `m <= 1` >-
  decide_tac >>
  `0 < m` by decide_tac >>
  assume_tac ordz_seekM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `n MOD m`, `m`, `1`] strip_assume_tac) >>
  `n MOD m < m` by rw[MOD_LESS] >>
  `size (MAX (n MOD m) m) = size m` by rw[MAX_DEF] >>
  `size (MAX 1 m) = size m` by rw[MAX_DEF] >>
  `stepsOf (ordzM m n) <= 2 * size m + size n * size m + stepsOf (ordz_seekM m (n MOD m) m 1)` by fs[] >>
  `stepsOf (ordz_seekM m (n MOD m) m 1) <= 1 + size m + 22 * m * size m ** 3 * size m ** 2 * size m ** 2` by fs[] >>
  `m * size m ** 3 * size m ** 2 * size m ** 2 = m * (size m) ** 7` by rw[GSYM EXP_EXP_MULT] >>
  decide_tac);

(* Theorem: stepsOf (ordzM m n) <= 27 * (MAX 1 m) * size n * size m ** 7 *)
(* Proof:
      stepsOf (ordzM m n)
   <= 1 + 3 * size m + size n * size m + 22 * m * size m ** 7   by ordzM_steps_upper
   <= (1 + 3 + 1 + 22) * m * size n * size m ** 7               by dominant term
    = 27 * m * size n * size m ** 7                             by arithmetic
   Use (MAX 1 m) to cater for m = 0.
*)
val ordzM_steps_bound = store_thm(
  "ordzM_steps_bound",
  ``!m n. stepsOf (ordzM m n) <= 27 * (MAX 1 m) * size n * size m ** 7``,
  rpt strip_tac >>
  assume_tac ordzM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `n`] strip_assume_tac) >>
  qabbrev_tac `k = MAX 1 m` >>
  qabbrev_tac `t = k * size n * size m ** 7` >>
  `stepsOf (ordzM m n) <= 27 * t` suffices_by rw[Abbr`t`] >>
  `1 <= k /\ m <= k` by rw[Abbr`k`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size m <= t` by
  (`size m <= size m * (k * size n * size m ** 6)` by rw[MULT_POS] >>
  `size m * (k * size n * size m ** 6) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size m * size n <= t` by
    (`size m * size n <= size m * size n * (k * size m ** 6)` by rw[MULT_POS] >>
  `size m * size n * (k * size m ** 6) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `m * size m ** 7 <= t` by
      (`m * size m ** 7 <= k * size m ** 7` by rw[] >>
  `k * size m ** 7 <= k * size m ** 7 * size n` by rw[MULT_POS] >>
  `k * size m ** 7 * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf o (ordzM m) IN O_poly 1 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (ordzM m n) <= k * size n
   Note stepsOf (ordzM m n)
     <= 27 * (MAX 1 m) * size n * size m ** 7    by ordzM_steps_bound
   Take any h, k = 27 * MAX 1 m * size m ** 7, the result follows.
*)
val ordzM_steps_O_poly = store_thm(
  "ordzM_steps_O_poly",
  ``!m. stepsOf o (ordzM m) IN O_poly 1``,
  rw[O_poly_thm] >>
  qexists_tac `0` >>
  qexists_tac `27 * MAX 1 m * size m ** 7` >>
  rpt strip_tac >>
  assume_tac ordzM_steps_bound >>
  last_x_assum (qspecl_then [`m`, `n`] strip_assume_tac) >>
  fs[]);

(* A spectacular result derived from loop recurrence theory! *)

(* Theorem: stepsOf o (ordzM m) IN big_O (\n. (ulog n)) *)
(* Proof:
   Note (stepsOf o (ordzM m)) IN O_poly 1   by ordzM_steps_O_poly
    and O_poly 1
      = big_O (POLY 1 o ulog)               by O_poly_eq_O_poly_ulog
      = (\n. ulog n)                        by POLY_def, FUN_EQ_THM
   The result follows.
*)
val ordzM_steps_big_O = store_thm(
  "ordzM_steps_big_O",
  ``!m. stepsOf o (ordzM m) IN big_O (\n. (ulog n))``,
  assume_tac ordzM_steps_O_poly >>
  `O_poly 1 = big_O (POLY 1 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 1 o ulog = \n. ulog n` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: stepsOf o (combin$C ordzM n) IN big_O (POLY 1 o (\m. (MAX 1 m) * size m ** 7)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show;
      ?k c. !m. k < m ==> stepsOf (ordzM m n) <= c * size m ** 7 * MAX 1 m
   Note stepsOf (ordzM m n)
     <= 27 * (MAX 1 m) * size n * size m ** 7    by ordzM_steps_bound
   Take any k, c = 27 * size n, the result follows.
*)
val ordzM_steps_O_swap = store_thm(
  "ordzM_steps_O_swap",
  ``!n. stepsOf o (combin$C ordzM n) IN big_O (POLY 1 o (\m. (MAX 1 m) * size m ** 7))``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `27 * size n` >>
  rpt strip_tac >>
  assume_tac ordzM_steps_bound >>
  last_x_assum (qspecl_then [`n'`, `n`] strip_assume_tac) >>
  fs[]);

(* Theorem: (valueOf (ordzM m n) = ordz m n) /\
            stepsOf o (ordzM m) IN big_O (\n. (ulog n)) *)
(* Proof: by ordzM_value, ordzM_steps_big_O *)
val ordzM_thm = store_thm(
  "ordzM_thm",
  ``!m n. (valueOf (ordzM m n) = ordz m n) /\
         stepsOf o (ordzM m) IN big_O (\n. (ulog n))``,
  metis_tac[ordzM_value, ordzM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
