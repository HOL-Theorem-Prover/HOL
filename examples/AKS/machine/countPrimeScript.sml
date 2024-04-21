(* ------------------------------------------------------------------------- *)
(* Primality Test in monadic style.                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countPrime";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory dividesTheory numberTheory
     combinatoricsTheory logrootTheory pairTheory optionTheory primeTheory;

open countMonadTheory countMacroTheory;
open countBasicTheory countPowerTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory;

(* (* val _ = load "monadsyntax"; *) *)
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Primality Test in monadic style Documentation                             *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Traditional Primality Test:
   factor_seekM_def    |- !q n c. factor_seekM n c q =
                                  do
                                    b0 <- leqM c q;
                                    if b0 then unit n
                                    else
                                      do
                                        b1 <- ifM (leqM q 1) (return F) do r <- modM n q; zeroM r od;
                                        if b1 then unit q else do p <- incM q; factor_seekM n c p od
                                      od
                                  od
   prime_testM_def     |- !n. prime_testM n =
                              do
                                n0 <- zeroM n;
                                n1 <- oneM n;
                                if n0 \/ n1 then unit F
                                else
                                  do
                                    r <- sqrtM n;
                                    c <- incM r;
                                    p <- factor_seekM n c 2;
                                    eqM p n
                                  od
                              od
#  factor_seekM_value  |- !n c q. valueOf (factor_seekM n c q) = factor_seek n c q
#  prime_testM_value   |- !n. valueOf (prime_testM n) <=> prime_test n
   prime_testM_thm     |- !n. valueOf (prime_testM n) <=> prime n

   factor_seekM_steps_thm
                       |- !n c q. stepsOf (factor_seekM n c q) =
                                  size (MAX c q) + size (c - q) +
                                  if c <= q then 0
                                  else size (MAX q 1) + size (q - 1) +
                                       (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                                       if 1 < q /\ n MOD q = 0 then 0
                                       else size q + stepsOf (factor_seekM n c (q + 1))
   prime_testM_steps_thm
                       |- !n. stepsOf (prime_testM n) =
                              TWICE (size n) +
                              if n <= 1 then 0
                              else size (SQRT n) + size (MAX (factor_seek n (1 + SQRT n) 2) n) +
                                   stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)
   factor_seekM_steps_by_inc_loop
                       |- !n c. (let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                                              (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                                              if 1 < q /\ n MOD q = 0 then 0 else size q
                                  in !q. stepsOf (factor_seekM n c q) =
                                         if c <= q then 1 + size q
                                         else body q +
                                              if 1 < q /\ n MOD q = 0 then 0
                                              else stepsOf (factor_seekM n c (q + 1)))

   factor_seekM_prime_steps_thm
                       |- !n c q. prime n /\ c <= n ==>
                                  stepsOf (factor_seekM n c q) =
                                  size (MAX c q) + size (c - q) +
                                  if c <= q then 0
                                  else size (MAX q 1) + size (q - 1) + size q +
                                       (if 1 < q then size n * size q + size (n MOD q) else 0) +
                                       stepsOf (factor_seekM n c (q + 1))
   factor_seekM_prime_steps_by_inc_loop
                       |- !n c. prime n /\ c <= n ==>
                                (let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                                              size q + if 1 < q then size n * size q + size (n MOD q) else 0
                                  in !q. stepsOf (factor_seekM n c q) =
                                         if c <= q then 1 + size q
                                         else body q + stepsOf (factor_seekM n c (q + 1)))
   factor_seekM_prime_steps_eqn
                       |- !n c. prime n /\ c <= n ==>
                                (let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                                              size q + if 1 < q then size n * size q + size (n MOD q) else 0
                                  in !q. stepsOf (factor_seekM n c q) =
                                         1 + size (q + (c - q)) +
                                         SUM (GENLIST (\j. body (q + j)) (c - q)))
   prime_testM_prime_steps_thm
                       |- !n. prime n ==>
                              stepsOf (prime_testM n) =
                              3 * size n + size (SQRT n) + stepsOf (sqrtM n) +
                              stepsOf (factor_seekM n (1 + SQRT n) 2)
   prime_testM_prime_steps_eqn
                       |- !n. (let c = 1 + SQRT n ;
                                   body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                                            size q + if 1 < q then size n * size q + size (n MOD q) else 0
                                in prime n ==>
                                   stepsOf (prime_testM n) =
                                   1 + size c + 3 * size n + size (SQRT n) + stepsOf (sqrtM n) +
                                   SUM (GENLIST (\j. body (2 + j)) (c - 2)))
   prime_testM_prime_steps_lower
                       |- !n. prime n ==> SQRT n <= stepsOf (prime_testM n)


   Polynomial Growth vs Exponential Growth:
   power_lt_exp            |- !b. 1 < b ==> !c k. ?p. 0 < p /\ c * p ** k < b ** p
   power_lt_exp_extended   |- !c b k p. c * p ** k < b ** p /\ 0 < p /\ 2 ** k < b ==>
                              !d. c * (p + d) ** k < b ** (p + d)
   power_lt_exp_all        |- !b k. 2 ** k < b ==> !c. ?p. 0 < p /\ !n. p < n ==> c * n ** k < b ** n
   log_lt_root             |- !k b. 0 < k /\ 1 < b ==> ?p. 0 < p /\ LOG b p < ROOT k p
   log_lt_root_all         |- !k b. 0 < k /\ 1 < b ==> !n. ?p. n < p /\ LOG b p < ROOT k p
   ulog_power_nonlinear    |- !c k. ?n. 1 < n /\ c * ulog n ** k < n

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* for EVAL IFm *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* EVAL IFm must be in current script, e.g. EVAL ``expn 1 2 3``; *)

(* ------------------------------------------------------------------------- *)
(* Traditional Primality Test                                                *)
(* ------------------------------------------------------------------------- *)

(* Seek a factor q to divide a number n, up to a cutoff c. *)
Definition factor_seekM_def:
  factor_seekM n c q =
    do
      b0 <- leqM c q;
      if b0 then return n
      else do
             b1 <- ifM (leqM q 1) (return F) (do r <- modM n q; r0 <- zeroM r od);
             if b1 then return q
             else do
                    p <- incM q;
                    factor_seekM n c p;
                  od
           od
    od
Termination WF_REL_TAC `measure (λ(n,c,q). c - q)` >> simp[]
End
(* Note: ~(1 < q) = q <= 1, ensure 1 < q before n MOD q. *)

(* Primality test by seeking factor up to (1 + SQRT n) *)
val prime_testM_def = Define`
    prime_testM n =
      do
         n0 <- zeroM n;
         n1 <- oneM n;
         if n0 \/ n1 then return F
         else do
                r <- sqrtM n;
                c <- incM r;
                p <- factor_seekM n c 2;
                eqM p n;
              od
      od
`;

(*
EVAL ``MAP prime_testM [1 .. 15]``; =
      [(F,Count 2); (T,Count 59); (T,Count 59); (F,Count 147); (T,Count 152);
       (F,Count 146); (T,Count 151); (F,Count 159); (F,Count 180);
       (F,Count 161); (T,Count 187); (F,Count 161); (T,Count 186);
       (F,Count 161); (F,Count 180)]: thm
*)

(* Theorem: valueOf (factor_seekM n c q) = factor_seek n c q *)
(* Proof: by induction on factor_seekM_def, factor_seek_def. *)
val factor_seekM_value = store_thm(
  "factor_seekM_value[simp]",
  ``!n c q. valueOf (factor_seekM n c q) = factor_seek n c q``,
  ho_match_mp_tac (theorem "factor_seekM_ind") >>
  rw[] >>
  rw[Once factor_seekM_def, Once factor_seek_def]);

(* Theorem: valueOf (prime_testM n) = prime_test n *)
(* Proof: by prime_testM_def, prime_test_def *)
val prime_testM_value = store_thm(
  "prime_testM_value[simp]",
  ``!n. valueOf (prime_testM n) = prime_test n``,
  rw[prime_testM_def, prime_test_def]);

(* Theorem: valueOf (prime_testM n) = prime n *)
(* Proof: by prime_testM_value, prime_test_thm *)
val prime_testM_thm = store_thm(
  "prime_testM_thm",
  ``!n. valueOf (prime_testM n) = prime n``,
  rw[prime_test_thm]);

(* Theorem: stepsOf (factor_seekM n c q) =
           size (MAX c q) + size (c - q) +
           if c <= q then 0
           else (size (MAX q 1) + size (q - 1) +
                if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                if 1 < q /\ n MOD q = 0 then 0
                else size q + stepsOf (factor_seekM n c (q + 1)) *)
(* Proof:
     stepsOf (factor_seekM n c q)
   = stepsOf (leqM c q) + if c <= q then 0
     else (stepsOf (leqM q 1) + if q <= 1 then 0 else stepsOf (modM n q) + stepsOf (zeroM (n MOD q))) +
          if 1 < q /\ n MOD q = 0 then 0
          else (stepsOf (incM q) + stepsOf (factor_seekM n c (q + 1)))  by factor_seekM_def
   = size (MAX c q) + size (c - q) + if c <= q then 0        by leqM_steps, size_max
     else (size (MAX q 1) + size (q - 1) +
           if q <= 1 then 0 else size n * size q + size (n MOD q)) +
           if 1 < q /\ n MOD q = 0 then 0
          else size q + stepsOf (factor_seekM n c (q + 1))
*)
val factor_seekM_steps_thm = store_thm(
  "factor_seekM_steps_thm",
  ``!n c q. stepsOf (factor_seekM n c q) =
           size (MAX c q) + size (c - q) +
           if c <= q then 0
           else (size (MAX q 1) + size (q - 1) +
                if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                if 1 < q /\ n MOD q = 0 then 0
                else size q + stepsOf (factor_seekM n c (q + 1))``,
  rw[Once factor_seekM_def, size_max]);

(* Theorem: stepsOf (prime_testM n) =
       2 * size n +
       if n <= 1 then 0
       else size (SQRT n) + size (MAX (factor_seek n (1 + SQRT n) 2) n) +
            stepsOf (sqrtM n) +
            stepsOf (factor_seekM n (1 + SQRT n) 2) *)
(* Proof:
     stepsOf (prime_testM n) =
   = stepsOf (zeroM n) + stepsOf (oneM n) + if n = 0 \/ n = 1 then 0
     else stepsOf (sqrtM n) + stepsOf (incM (SQRT n)) +
          stepsOf (factor_seekM n (1 + SQRT n) 2) +
          stepsOf (eqM (factor_seek n (1 + SQRT n) 2) n)      by prime_testM_def
   = size n + size n + if n <= 1 then 0
     else stepsOf (sqrtM n) + size (SQRT n) +
          stepsOf (factor_seekM n (1 + SQRT n) 2) +
          size (MAX (factor_seek n (1 + SQRT n) 2) n)
*)
val prime_testM_steps_thm = store_thm(
  "prime_testM_steps_thm",
  ``!n. stepsOf (prime_testM n) =
       2 * size n +
       if n <= 1 then 0
       else size (SQRT n) + size (MAX (factor_seek n (1 + SQRT n) 2) n) +
            stepsOf (sqrtM n) +
            stepsOf (factor_seekM n (1 + SQRT n) 2)``,
  rw[prime_testM_def, size_max]);

(* Theorem: let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                      (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                      if 1 < q /\ n MOD q = 0 then 0 else size q
          in !q. stepsOf (factor_seekM n c q) =
                 if c <= q then (1 + size q)
                 else body q +
                      if 1 < q /\ n MOD q = 0 then 0 else stepsOf (factor_seekM n c (q + 1)) *)
(* Proof:
     stepsOf (factor_seekM n c q)
   = size (MAX c q) + size (c - q) +
     if c <= q then 0
     else (size (MAX q 1) + size (q - 1) +
           if q <= 1 then 0 else size n * size q + size (n MOD q)) +
          if 1 < q /\ n MOD q = 0 then 0
          else size q + stepsOf (factor_seekM n c (q + 1))        by factor_seekM_steps_thm
   = if c <= q then (size (MAX c q) + size (c - q))
     else (size (MAX c q) + size (c - q) +
           size (MAX q 1) + size (q - 1) +
           (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
           if 1 < q /\ n MOD q = 0 then 0 else size q) +
          if 1 < q /\ n MOD q = 0 then 0 else stepsOf (factor_seekM n c (q + 1))
   = if c <= q then (size q + size 0)                            by MAX_DEF, c - q = 0
     else (size c + size (c - q) +                               by MAX_DEF
           size (MAX q 1) + size (q - 1) +
           (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
           if 1 < q /\ n MOD q = 0 then 0 else size q) +
          if 1 < q /\ n MOD q = 0 then 0 else stepsOf (factor_seekM n c (q + 1))
*)
val factor_seekM_steps_by_inc_loop = store_thm(
  "factor_seekM_steps_by_inc_loop",
  ``!n c. let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) +
                      (if q <= 1 then 0 else size n * size q + size (n MOD q)) +
                      if 1 < q /\ n MOD q = 0 then 0 else size q
          in !q. stepsOf (factor_seekM n c q) =
                 if c <= q then (1 + size q)
                 else body q +
                      if 1 < q /\ n MOD q = 0 then 0 else stepsOf (factor_seekM n c (q + 1))``,
  rw[Once factor_seekM_steps_thm] >>
  (Cases_on `c <= q` >> simp[MAX_DEF]) >>
  `(if c < q then q else c) = q` by decide_tac >>
  `c - q = 0` by decide_tac >>
  rw[]);

(*
This puts factor_seekM_steps in the category: increasing loop with body cover and exit.
   factor_seekM_steps_by_inc_loop:
        !q. loop q = if c <= q then quit q else body q + if exit q then 0 else loop (q + 1)
suitable for: loop_inc_count_cover_exit_le
However, we are after the lower bound, not upper bound.
cannot even default to: loop_inc_count_eqn.
The lower bound can be very small, e.g. for even n.
However, for a prime n, n MOD q <> 0 for
*)

(* Theorem: prime n /\ c <= n ==>
           (stepsOf (factor_seekM n c q) =
            size (MAX c q) + size (c - q) +
            if c <= q then 0
            else size (MAX q 1) + size (q - 1) + size q +
                 (if 1 < q then size n * size q + size (n MOD q) else 0) +
                      stepsOf (factor_seekM n c (q + 1))) *)
(* Proof:
   Note in factor_seekM_def,
        1 < q /\ n MOD q = 0 means q divides n     by DIVIDES_MOD_0, 0 < q
    But q <> 1                                     by 1 < q
    and q <> n                                     by q < c, c <= n
   This will contradict prime n                    by prime_def
   Thus n MOD q <> 0, the result follows           by factor_seekM_def
*)
val factor_seekM_prime_steps_thm = store_thm(
  "factor_seekM_prime_steps_thm",
  ``!n c q. prime n /\ c <= n ==>
           (stepsOf (factor_seekM n c q) =
            size (MAX c q) + size (c - q) +
            if c <= q then 0
            else size (MAX q 1) + size (q - 1) + size q +
                 (if 1 < q then size n * size q + size (n MOD q) else 0) +
                      stepsOf (factor_seekM n c (q + 1)))``,
  rw[Once factor_seekM_def, size_max] >>
  (Cases_on `1 < q /\ n MOD q = 0` >> simp[]) >>
  `q divides n` by rw[DIVIDES_MOD_0] >>
  `q <> 1 /\ q <> n` by decide_tac >>
  metis_tac[prime_def]);

(* Theorem: prime n /\ c <= n ==>
         let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
          in !q. stepsOf (factor_seekM n c q) =
                 if c <= q then (1 + size q)
                 else body q + stepsOf (factor_seekM n c (q + 1)) *)
(* Proof:
     stepsOf (factor_seekM n c q)
   = size (MAX c q) + size (c - q) +
     if c <= q then 0
     else size (MAX q 1) + size (q - 1) + size q +
          (if 1 < q then size n * size q + size (n MOD q) else 0) +
          stepsOf (factor_seekM n c (q + 1))            by factor_seekM_prime_steps_thm
   = if c <= q then size (MAX c q) + size (c - q)
     else size (MAX c q) + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
          (if 1 < q then size n * size q + size (n MOD q) else 0) +
          stepsOf (factor_seekM n c (q + 1))
   = if c <= q then size q + size 0                by MAX_DEF
     else size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
          (if 1 < q then size n * size q + size (n MOD q) else 0) +
          stepsOf (factor_seekM n c (q + 1))
*)
val factor_seekM_prime_steps_by_inc_loop = store_thm(
  "factor_seekM_prime_steps_by_inc_loop",
  ``!n c. prime n /\ c <= n ==>
         let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
          in !q. stepsOf (factor_seekM n c q) =
                 if c <= q then (1 + size q)
                 else body q + stepsOf (factor_seekM n c (q + 1))``,
  rw[Once factor_seekM_prime_steps_thm] >>
  (Cases_on `c <= q` >> simp[MAX_DEF]) >>
  `(if c < q then q else c) = q` by decide_tac >>
  `c - q = 0` by decide_tac >>
  rw[]);

(*
This puts factor_seekM_prime_steps in the category: increasing loop with body.
   factor_seekM_prime_steps_by_inc_loop:
        !q. loop q = if c <= q then quit q else body q + loop (q + 1)
suitable for: loop_inc_count_eqn to deduce lower bound.
*)

(* Theorem: prime n /\ c <= n ==>
         let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
          in !q. stepsOf (factor_seekM n c q) =
                 1 + size (q + (c - q)) + SUM (GENLIST (\j. body (q + j)) (c - q)) *)
(* Proof:
   Let quit = (\q. 1 + size q),
       body = (\q. size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0)
       loop = (\q. stepsOf (factor_seekM n c q)).
   Then !q. loop q = if c <= q then quit q else body q + loop (q + 1)
                                                by factor_seekM_prime_steps_by_inc_loop
   Let p = bop 1 c q = c - q                    by bop_1_m_c
   Thus loop q
      = quit (q + p) + SUM (GENLIST (\j. body (q + j)) p)   by loop_inc_count_eqn
      = 1 + size (q + (c - q)) + SUM (GENLIST (\j. body (q + j)) (c - q))
*)
val factor_seekM_prime_steps_eqn = store_thm(
  "factor_seekM_prime_steps_eqn",
  ``!n c. prime n /\ c <= n ==>
         let body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
          in !q. stepsOf (factor_seekM n c q) =
                 1 + size (q + (c - q)) + SUM (GENLIST (\j. body (q + j)) (c - q))``,
  rpt strip_tac >>
  imp_res_tac factor_seekM_prime_steps_by_inc_loop >>
  qabbrev_tac `body = \q. size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0` >>
  qabbrev_tac `quit = \q. 1 + size q` >>
  qabbrev_tac `loop = \q. stepsOf (factor_seekM n c q)` >>
  `!q. loop q =
        quit (q + (c - q)) + SUM (GENLIST (\j. body (q + j)) (c - q))` suffices_by metis_tac[] >>
  rpt strip_tac >>
  `!q. loop q = if c <= q then quit q else body q + loop (q + 1)` by metis_tac[] >>
  `0 < 1` by decide_tac >>
  `bop 1 c q = c - q` by rw[bop_1_m_c] >>
  imp_res_tac loop_inc_count_eqn >>
  first_x_assum (qspec_then `q` strip_assume_tac) >>
  rw[]);

(* Theorem: prime n ==>
       stepsOf (prime_testM n) =
       3 * size n + size (SQRT n) + stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2) *)
(* Proof:
     stepsOf (prime_testM n)
   = 2 * size n +
     if n <= 1 then 0
     else size (SQRT n) + size (MAX (factor_seek n (1 + SQRT n) 2) n) +
          stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)   by prime_testM_steps_thm
   = 2 * size n + size (SQRT n) + size (MAX (factor_seek n (1 + SQRT n) 2) n) +
     stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)        by ONE_LT_PRIME
   = 2 * size n + size (SQRT n) + size n +
     stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)        by factor_seek_bound, 0 < n
   = 3 * size n + size (SQRT n) +
     stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)
*)
val prime_testM_prime_steps_thm = store_thm(
  "prime_testM_prime_steps_thm",
  ``!n. prime n ==>
       stepsOf (prime_testM n) =
       3 * size n + size (SQRT n) + stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)``,
  rpt strip_tac >>
  `1 < n` by rw[ONE_LT_PRIME] >>
  `factor_seek n (1 + SQRT n) 2 <= n` by rw[factor_seek_bound] >>
  `MAX (factor_seek n (1 + SQRT n) 2) n = n` by fs[MAX_DEF] >>
  rw[prime_testM_steps_thm]);

(* Theorem: let c = 1 + SQRT n;
           body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
        in prime n ==> stepsOf (prime_testM n) =
           1 + size c + 3 * size n + size (SQRT n) +
           stepsOf (sqrtM n) + SUM (GENLIST (\j. body (2 + j)) (c - 2)) *)
(* Proof:
   Let c = 1 + SQRT n.
   Note prime n ==> 1 < n           by ONE_LT_PRIME
    and SQRT n <= n                 by SQRT_LE_SELF
    and SQRT n <> n                 by SQRT_EQ_SELF, 1 < n
   Thus SQRT n < n                  by above
     or c = 1 + SQRT n <= n         by inequality
   Also SQRT n <> 0                 by SQRT_EQ_0, n <> 0
   Thus 1 < c, or 2 <= c            by notation
     or 2 + (c - 2) = c.

     stepsOf (prime_testM n)
   = 3 * size n + size (SQRT n) +
     stepsOf (sqrtM n) + stepsOf (factor_seekM n (1 + SQRT n) 2)   by prime_testM_prime_steps_thm
   = 3 * size n + size (SQRT n) +
     stepsOf (sqrtM n) +
     1 + size c + SUM (GENLIST (\j. body (2 + j)) (c - 2))  by factor_seekM_prime_steps_eqn, c <= n
*)
val prime_testM_prime_steps_eqn = store_thm(
  "prime_testM_prime_steps_eqn",
  ``!n. let c = 1 + SQRT n;
           body q = size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
                      if 1 < q then size n * size q + size (n MOD q) else 0
        in prime n ==> stepsOf (prime_testM n) =
           1 + size c + 3 * size n + size (SQRT n) +
           stepsOf (sqrtM n) + SUM (GENLIST (\j. body (2 + j)) (c - 2))``,
  rw_tac std_ss[] >>
  `c <= n` by
  (`1 < n` by rw[ONE_LT_PRIME] >>
  `SQRT n <= n` by rw[SQRT_LE_SELF] >>
  `SQRT n <> n` by rw[SQRT_EQ_SELF] >>
  qunabbrev_tac `c` >>
  decide_tac) >>
  `1 < c` by
    (`1 < n` by rw[ONE_LT_PRIME] >>
  `SQRT n <> 0` by rw[SQRT_EQ_0] >>
  qunabbrev_tac `c` >>
  decide_tac) >>
  `2 + (c - 2) = c` by decide_tac >>
  imp_res_tac prime_testM_prime_steps_thm >>
  qunabbrev_tac `c` >>
  qabbrev_tac `c = 1 + SQRT n` >>
  imp_res_tac factor_seekM_prime_steps_eqn >>
  qunabbrev_tac `body` >>
  qabbrev_tac `body = \q. size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
             if 1 < q then size n * size q + size (n MOD q) else 0` >>
  `!q. stepsOf (factor_seekM n c q) =
        1 + size (q + (c - q)) + SUM (GENLIST (\j. body (q + j)) (c - q))` by metis_tac[] >>
  first_x_assum (qspec_then `2` strip_assume_tac) >>
  rw[]);

(* Theorem: prime n ==> (SQRT n <= stepsOf (prime_testM n)) *)
(* Proof:
     stepsOf (prime_testM n)
   = 1 + size c + 3 * size n + size (SQRT n) + stepsOf (sqrtM n) +
     SUM (GENLIST (\j. body (2 + j)) (c - 2)))       by prime_testM_prime_steps_eqn
   Ignore all but size c and the SUM (GENLIST ... (c - 2)),
   Note SUM (GENLIST (K (size c)) (c - 2))
     <= SUM (GENLIST (\j. body (2 + j)) (c - 2))     by SUM_LE
    and SUM (GENLIST (K (size c)) (c - 2))
      = size c * (c - 2)                             by SUM_GENLIST_K
   Thus stepsOf (prime_testM n)
     >= size c + (c - 2) * size c
      = (c - 1) * size c
      = (SQRT n) * size (1 + SQRT n)
     >= (SQRT n) * size (SQRT n)                     by size_monotone_le
     >= SQRT n                                       by size_pos
*)
val prime_testM_prime_steps_lower = store_thm(
  "prime_testM_prime_steps_lower",
  ``!n. prime n ==> (SQRT n <= stepsOf (prime_testM n))``,
  rpt strip_tac >>
  assume_tac prime_testM_prime_steps_eqn >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `c = 1 + SQRT n` >>
  qabbrev_tac `body = \q. size c + size (c - q) + size (MAX q 1) + size (q - 1) + size q +
             if 1 < q then size n * size q + size (n MOD q) else 0` >>
  `stepsOf (prime_testM n) = 1 + size c + 3 * size n + size (SQRT n) + stepsOf (sqrtM n) +
                              SUM (GENLIST (\j. body (2 + j)) (c - 2))` by fs[] >>
  `SUM (GENLIST (K (size c)) (c - 2)) <=
    SUM (GENLIST (\j. body (2 + j)) (c - 2))` by rw[SUM_LE, Abbr`body`] >>
  `SUM (GENLIST (K (size c)) (c - 2)) = size c * (c - 2)` by rw[SUM_GENLIST_K] >>
  `size c + size c * (c - 2) <= stepsOf (prime_testM n)` by decide_tac >>
  `1 < c` by
  (`1 < n` by rw[ONE_LT_PRIME] >>
  `SQRT n <> 0` by rw[SQRT_EQ_0] >>
  qunabbrev_tac `c` >>
  decide_tac) >>
  `1 + (c - 2) = c - 1` by decide_tac >>
  `size c + size c * (c - 2) = size c * (1 + (c - 2))` by rw[LEFT_ADD_DISTRIB] >>
  `_ = (c - 1) * size c` by rw[] >>
  `!n. n <= n * size c` by rw[] >>
  `c - 1 <= (c - 1) * size c` by metis_tac[] >>
  `c - 1 = SQRT n` by rw[Abbr`c`] >>
  decide_tac);

(* Thus the traditional primality test by trial factors is not polynomial-time in (ulog n). *)


(* ------------------------------------------------------------------------- *)
(* Polynomial Growth vs Exponential Growth                                   *)
(* ------------------------------------------------------------------------- *)


(* For a fixed base b > 1, constant c and index k,
   there is a point p > 0 at which c ** p ** k < b ** p. *)
(* Theorem 1 < b ==> !c k. ?p. 0 < p /\ c * p ** k < b ** p *)
(* Proof:
   By induction on k.
   Base: !c. ?p. 0 < p /\ c * p ** 0 < b ** p
      Note c * p ** 0 = c * 1 = c           by EXP_0
      If c = 0, take p = 1, then 0 < b
      If c <> 0,
      Take p = c, then 0 < c /\ c < b ** c  by X_LT_EXP_X
   Step: !c. ?p. 0 < p /\ c * p ** k < b ** p ==>
         !c. ?p. 0 < p /\ c * p ** SUC k < b ** p
      Let d = c * 2 ** SUC k.
      Then ?p. 0 < p /\ d * p ** k < b ** p by induction hypothesis
       and              p < b ** p          by X_LT_EXP_X
        so d * p ** k * p < (b ** p) ** 2   by LT_MONO_MULT2
           d * p ** SUC k < b ** (2 * p)    by EXP, EXP_EXP_MULT
     c * (2 * p) ** SUC k < b ** (2 * p)    by EXP_BASE_MULT
      Take 2 * p, the result follows by 0 < 2 * p.
*)
val power_lt_exp = store_thm(
  "power_lt_exp",
  ``!b. 1 < b ==> !c k. ?p. 0 < p /\ c * p ** k < b ** p``,
  ntac 2 strip_tac >>
  `0 < b` by decide_tac >>
  Induct_on `k` >| [
    rw[] >>
    Cases_on `c = 0` >-
    metis_tac[EXP_1, DECIDE``0 < 1``] >>
    metis_tac[X_LT_EXP_X, NOT_ZERO],
    rpt strip_tac >>
    qabbrev_tac `d = c * 2 ** SUC k` >>
    `?p. 0 < p /\ d * p ** k < b ** p` by fs[] >>
    `p < b ** p` by rw[X_LT_EXP_X] >>
    `d * p ** k * p < b ** p * b ** p` by rw[LT_MONO_MULT2] >>
    `SQ (b ** p) = b ** (2 * p)` by rw[GSYM EXP_EXP_MULT] >>
    `d * p ** k * p = d * p ** SUC k` by rw[EXP] >>
    `_ = c * (2 * p) ** SUC k` by rw[EXP_BASE_MULT, Abbr`d`] >>
    `c * (2 * p) ** SUC k < b ** (2 * p)` by decide_tac >>
    `0 < 2 * p` by decide_tac >>
    metis_tac[]
  ]);

(* Theorem: c * p ** k < b ** p /\ 0 < p /\ 2 ** k < b ==>
        !d. c * (p + d) ** k < b ** (p + d) *)
(* Proof:
   By induction on d.
   Base: c * (p + 0) ** k < b ** (p + 0)
         c * (p + 0) ** k
       = c * p ** k                  by ADD_0
       < b ** p                      by given
       = b ** (p + 0)                by ADD_0
   Step: c * (p + d) ** k < b ** (p + d) ==>
         c * (p + SUC d) ** k < b ** (p + SUC d)
       Let z = p + d.
       Then SUC z = p + SUC d        by ADD
       the goal is: c * SUC z ** k < b ** SUC z

       Note 0 < z                    by 0 < p
         so 1 <= z, or SUC z <= z + z = 2 * z
            c * SUC z ** k
         <= c * (2 * z) ** k         by SUC z <= 2 * z
          = (2 ** k) * (c * z ** k)  by EXP_BASE_MULT
          < b * b ** z               by 2 ** k < b, induction hypothesis
          = b ** SUC z               by EXP
*)
val power_lt_exp_extended = store_thm(
  "power_lt_exp_extended",
  ``!c b k p. c * p ** k < b ** p /\ 0 < p /\ 2 ** k < b ==>
         !d. c * (p + d) ** k < b ** (p + d)``,
  ntac 5 strip_tac >>
  Induct >-
  rw[] >>
  qabbrev_tac `z = p + d` >>
  `p + SUC d = SUC z` by rw[Abbr`z`] >>
  simp[] >>
  `0 < z` by rw[Abbr`z`] >>
  `SUC z <= 2 * z` by decide_tac >>
  `c * (SUC z) ** k <= c * (2 * z) ** k` by rw[] >>
  `c * (2 * z) ** k = 2 ** k * (c * z ** k)` by rw[EXP_BASE_MULT] >>
  `2 ** k * (c * z ** k) < b * b ** z` by rw[LT_MONO_MULT2] >>
  `b * b ** z = b ** SUC z` by rw[EXP] >>
  decide_tac);

(* For a fixed base b > 2 ** k, constant c and index k, there is a point p > 0
   after which for all n > p, c ** n ** k < b ** n. *)
(* Theorem: 2 ** k < b ==> !c. ?p. 0 < p /\ (!n. p < n ==> c * n ** k < b ** n) *)
(* Proof:
   Note 0 < 2 ** k         by EXP_POS
     so 1 < b              by 1 <= 2 ** k < b
   Thus ?p. 0 < p /\ c * p ** k < b ** p    by power_lt_exp
   Take this p, let d = n - p.
   Then n = p + d          by p < n
   The result follows      by power_lt_exp_extended
*)
val power_lt_exp_all = store_thm(
  "power_lt_exp_all",
  ``!b k. 2 ** k < b ==> !c. ?p. 0 < p /\ (!n. p < n ==> c * n ** k < b ** n)``,
  rpt strip_tac >>
  `0 < 2 ** k` by rw[] >>
  `1 < b` by decide_tac >>
  `?p. 0 < p /\ c * p ** k < b ** p` by rw[power_lt_exp] >>
  qexists_tac `p` >>
  rw[] >>
  qabbrev_tac `d = n - p` >>
  `n = p + d` by rw[Abbr`d`] >>
  rw[power_lt_exp_extended]);

(*
For continuous functions, we can say: f(x) < g(x)  iff  g^-1(x) < f^-1(x)
Thus with    n ** k < b ** n  for sufficiently large n
we have    ROOT k n > LOG b n for sufficiently large n
However, we are using integer functions here.
*)


(* Theorem: 0 < k /\ 1 < b ==> ?p. 0 < p /\ LOG b p < ROOT k p *)
(* Proof:
   By contradiction, suppose !p. 0 < p ==> ROOT k p <= LOG b p.
   Note ?c. 0 < c /\ k * c ** 1 < b ** c     by power_lt_exp, 1 < b
     or     0 < c /\ k * c < b ** c          [1]

   Let p = (b ** c) ** k.
   Then 1 < b ** c                    by ONE_LT_EXP, 1 < b, 0 < c
    and 0 < p                         by EXP_POS, 0 < b ** c
    ==> ROOT k p <= LOG b p           by implication [2]
    But ROOT k p = b ** c             by ROOT_POWER, 1 < b ** c
    and LOG b p
      = LOG b (b ** (c * k))          by EXP_EXP_MULT
      = c * k                         by LOG_EXACT_EXP
   Thus b ** c <= c * k               by [2]
   which contradicts k * c < b ** c   by [1]
*)
val log_lt_root = store_thm(
  "log_lt_root",
  ``!k b. 0 < k /\ 1 < b ==> ?p. 0 < p /\ LOG b p < ROOT k p``,
  spose_not_then strip_assume_tac >>
  `!p. 0 < p ==> (ROOT k p <= LOG b p)` by metis_tac[NOT_LESS] >>
  `?c. 0 < c /\ k * c ** 1 < b ** c` by rw[power_lt_exp] >>
  fs[] >>
  qabbrev_tac `p = (b ** c) ** k` >>
  `1 < b ** c` by rw[ONE_LT_EXP] >>
  `0 < p` by rw[Abbr`p`] >>
  `ROOT k p = b ** c` by rw[ROOT_POWER, Abbr`p`] >>
  `LOG b p = c * k` by rw[LOG_EXACT_EXP, GSYM EXP_EXP_MULT, Abbr`p`] >>
  `ROOT k p <= LOG b p` by fs[] >>
  decide_tac);

(* Theorem: 0 < k /\ 1 < b ==> !n. ?p. n < p /\ LOG b p < ROOT k p *)
(* Proof:
   By contradiction, suppose !p. n < p ==> ROOT k p <= LOG b p.
   If n = 0,
      Note ?p. 0 < p /\ LOG b p < ROOT k p   by log_lt_root
      This p gives a contradiction.
   If n <> 0,
      Let c = SUC (LOG b n).
      Note ?q. 0 < q /\ c * k * q ** k < b ** q  by power_lt_exp, [1]
      Let p = (b ** (c * (q ** k))) ** k = b ** (c * k * q ** k)

      Claim: n < p
      Proof: Note p = (b ** c) ** (q ** k * k)   by EXP_EXP_MULT
              and n < b ** c                     by LOG_THM, 0 < n
              and 0 < q ** k                     by EXP_POS, 0 < q
               so 0 < q ** k * k                 by MULT_POS, 0 < k
              ==> b ** c
               <= (b ** c) ** (q ** k * k)       by X_LE_X_EXP, 0 < q ** k * k
                = p
             Thus n < b ** c <= p, or n < p.

      Note 0 < c                             by SUC_POS
       and 0 < q ** k                        by EXP_POS, 0 < q
        so 0 < c * (q ** k)                  by MULT_POS
       ==> 1 < b ** (c * (q ** k))           by ONE_LT_EXP, 1 < b, 0 < c * (q ** k)
      Thus ROOT k p = b ** (c * (q ** k))    by ROOT_POWER
      also p = b ** (c * (q ** k) * k)       by EXP_EXP_MULT
      Thus LOG b p = c * (q ** k) * k        by LOG_EXACT_EXP

      Claim: b ** q <= b ** (c * q ** k)     [2]
      Proof: Note q <= q ** k                by X_LE_X_EXP, 0 < k
               so q ** k <= c * q ** k       by SUC_POS, 0 < c
             Thus q <= c * q ** k            by LESS_EQ_TRANS
             b ** q <= b ** (c * q ** k)     by EXP_BASE_LE_MONO

      From [1], c * k * q ** k < b ** q
            so  c * k * q ** k < b ** (c * q ** k)    by Claim [2]
            or         LOG b p < ROOT k p
      This contradicts ROOT k p <= LOG b p.
*)
val log_lt_root_all = store_thm(
  "log_lt_root_all",
  ``!k b. 0 < k /\ 1 < b ==> !n. ?p. n < p /\ LOG b p < ROOT k p``,
  spose_not_then strip_assume_tac >>
  Cases_on `n = 0` >-
  metis_tac[log_lt_root] >>
  `0 < n` by decide_tac >>
  qabbrev_tac `c = SUC (LOG b n)` >>
  `?q. 0 < q /\ c * k * q ** k < b ** q` by rw[power_lt_exp] >>
  qabbrev_tac `p = (b ** (c * (q ** k))) ** k` >>
  `n < p` by
  (`p = (b ** c) ** (q ** k * k)` by rw[GSYM EXP_EXP_MULT, Abbr`p`] >>
  `n < b ** c` by metis_tac[LOG_THM] >>
  `0 < q ** k * k` by rw[MULT_POS] >>
  `b ** c <= p` by rw[X_LE_X_EXP] >>
  decide_tac) >>
  `0 < c * (q ** k)` by rw[MULT_POS, Abbr`c`] >>
  `1 < b ** (c * (q ** k))` by rw[ONE_LT_EXP] >>
  `ROOT k p = b ** (c * (q ** k))` by rw[ROOT_POWER, Abbr`p`] >>
  `p = b ** (c * (q ** k) * k)` by rw[EXP_EXP_MULT, Abbr`p`] >>
  `LOG b p = c * (q ** k) * k` by rw[LOG_EXACT_EXP] >>
  `b ** q <= b ** (c * q ** k)` by
    (`q <= q ** k` by rw[X_LE_X_EXP] >>
  `q ** k <= c * q ** k` by rw[Abbr`c`] >>
  `q <= c * q ** k` by decide_tac >>
  rw[EXP_BASE_LE_MONO]) >>
  `LOG b p < ROOT k p` by decide_tac >>
  metis_tac[]);


(* To show this is false:    !n c k. n <= c * (ulog n) ** k *)

(* Theorem: ?n. 1 < n /\ c * (ulog n) ** k < n *)
(* Proof:
   By induction on k.
   Base: !c. ?n. 1 < n /\ c * ulog n ** 0 < n
      Note  c * ulog n ** 0
          = c * 1                  by EXP_0
          < SUC c                  by LESS_SUC
      If c = 0, take n = 2 > 1.
      If c <> 0, take n = SUC c > 1
      The result follows.
   Step: !c. ?n. 1 < n /\ c * ulog n ** k < n ==>
         !c. ?n. 1 < n /\ c * ulog n ** SUC k < n
      For the result,
      assume n = a * a = a ** 2            by EXP_2
          c * ulog n ** SUC k
        = c * (ulog (a ** 2)) ** SUC k     by assumption
       <= c * (2 * ulog a) ** SUC k        by ulog_exp
        = (c * 2 ** SUC k) * (ulog a) ** SUC k           by EXP_BASE_MULT
        = (c * 2 ** SUC k * (ulog a) ** k) * (ulog a)    by EXP
        < a * (ulog a)                                   by induction hypothesis
        < a * a                                          by ulog_lt_self
        = n
      Thus assert the existence of a  by induction hypothesis with (c * 2 ** k),
      Then let n = a ** 2, the result follows            by ONE_LT_EXP, 1 < a
*)
val ulog_power_nonlinear = store_thm(
  "ulog_power_nonlinear",
  ``!c k. ?n. 1 < n /\ c * (ulog n) ** k < n``,
  Induct_on `k` >| [
    rpt strip_tac >>
    Cases_on `c = 0` >| [
      qexists_tac `2` >>
      simp[],
      qexists_tac `SUC c` >>
      simp[]
    ],
    rpt strip_tac >>
    `?a. 1 < a /\ c * 2 ** SUC k * ulog a ** k < a` by fs[] >>
    qexists_tac `a ** 2` >>
    `1 < a ** 2` by rw[ONE_LT_EXP] >>
    `ulog (a ** 2) <= 2 * ulog a` by rw[ulog_exp] >>
    `c * ulog (a ** 2) ** SUC k <= c * (2 * ulog a) ** SUC k` by rw[] >>
    `c * (2 * ulog a) ** SUC k = c * 2 ** SUC k * (ulog a) ** SUC k` by rw[EXP_BASE_MULT] >>
    `_ = c * 2 ** SUC k * ((ulog a) * (ulog a) ** k)` by rw[EXP] >>
    `_ = (c * 2 ** SUC k * (ulog a) ** k) * (ulog a)` by decide_tac >>
    qabbrev_tac `b = c * 2 ** SUC k * (ulog a) ** k` >>
    `ulog a < a` by rw[ulog_lt_self] >>
    `b * ulog a < a * a` by rw[LT_MONO_MULT2] >>
    `a * a = a ** 2` by rw[] >>
    decide_tac
  ]);



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
