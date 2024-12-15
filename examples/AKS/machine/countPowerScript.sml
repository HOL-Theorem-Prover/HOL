(* ------------------------------------------------------------------------- *)
(* Power Computations with Count Monad                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countPower";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory combinatoricsTheory logrootTheory pairTheory optionTheory
     listRangeTheory primeTheory;

open countMonadTheory countMacroTheory;
open countBasicTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory;

open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);
val _ = temp_overload_on ("RISING", ``\f. !x:num. x <= f x``);
val _ = temp_overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* ------------------------------------------------------------------------- *)
(* Power Computations with Count Monad Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Fast Exponentiation:
   expM_def          |- !n b. expM b n =
                                  do
                                    gd <- zeroM n;
                                    if gd then 1c
                                    else
                                      do
                                        b' <- sqM b;
                                        n' <- halfM n;
                                        r <- expM b' n';
                                        ifM (evenM n) (return r) (mulM b r)
                                      od
                                  od
#  expM_value        |- !b n. valueOf (expM b n) = b ** n
   expM_steps_thm    |- !b n. stepsOf (expM b n) =
                              if n = 0 then 1
                              else 1 + 5 * size n + size b ** 2 +
                                   (if EVEN n then 0 else size b * size (SQ b ** HALF n)) +
                                   stepsOf (expM (SQ b) (HALF n))
   expM_steps_b_0    |- !b. stepsOf (expM b 0) = 1
   expM_steps_by_sq_div_loop
                     |- (let body b n = 1 + 5 * size n + size b ** 2 +
                               if EVEN n then 0 else size b * size (SQ b ** HALF n)
                          in !b n. stepsOf (expM b n) =
                                   if n = 0 then 1
                                   else body b n + stepsOf (expM (SQ b) (HALF n)))
   expM_steps_by_sq_div_loop_alt
                     |- (let body b n = 1 + 5 * size n + size b ** 2 +
                               if EVEN n then 0 else size b * size ((b ** 2) ** HALF n)
                         in !b n. stepsOf (expM b n) =
                                  if n = 0 then 1
                                  else body b n + stepsOf (expM (b ** 2) (HALF n)))
   expM_steps_upper  |- !b n. stepsOf (expM b n) <=
                              1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2
   expM_steps_0_upper|- !n. stepsOf (expM 0 n) <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3
   expM_steps_1_upper|- !n. stepsOf (expM 1 n) <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3
   expM_steps_bound  |- !b n. stepsOf (expM b n) <= 15 * MAX 1 n ** 3 * size b ** 2 * size n ** 2
   expM_steps_O_base |- !b. stepsOf o expM b IN big_O (POLY 1 o (\n. n ** 3 * size b ** 2 * size n ** ))
   expM_steps_O_poly |- !b. stepsOf o expM b IN big_O (POLY 1 o (\n. n ** 3 * size n ** 2))
   expM_steps_O_swap |- !n. stepsOf o combin$C expM n IN O_poly 2
   expM_steps_big_O  |- !b. stepsOf o expM b IN big_O (\n. n ** 3 * ulog n ** 2)
   expM_thm          |- !b n. (valueOf (expM b n) = b ** n) /\
                              stepsOf o expM b IN big_O (\n. n ** 3 * ulog n ** 2)

   Root computation:
   shrinkM_def           |- !n k. shrinkM n k =
                                  do
                                    gd <- zeroM k;
                                    if gd then unit n
                                    else do n' <- halfM n; k' <- decM k; shrinkM n' k' od
                                  od
#  shrinkM_value         |- !n k. valueOf (shrinkM n k) = n DIV 2 ** k
   shrinkM_steps_thm     |- !n k. stepsOf (shrinkM n k) =
                                  size k +
                                  if k = 0 then 0
                                  else TWICE (size n) + size k + stepsOf (shrinkM (HALF n) (k - 1))
   shrinkM_steps_0       |- !n. stepsOf (shrinkM n 0) = 1
   shrinkM_steps_1       |- !n. stepsOf (shrinkM n 1) = 3 + TWICE (size n)
   shrinkM_steps_by_half_dec_loop
                         |- !n k. stepsOf (shrinkM n k) =
                                  if k = 0 then 1
                                  else TWICE (size k) + TWICE (size n) +
                                       stepsOf (shrinkM (HALF n) (k - 1))
   shrinkM_steps_upper   |- !n k. stepsOf (shrinkM n k) <= 1 + TWICE k * size k + TWICE k * size n
   shrinkM_steps_bound   |- !n k. stepsOf (shrinkM n k) <= 5 * MAX 1 k * size k * size n
   shrinkM_steps_O_base  |- !k. stepsOf o combin$C shrinkM k IN
                                big_O (POLY 1 o (\n. MAX 1 k * size k * size n))
   shrinkM_steps_O_poly  |- !k. stepsOf o combin$C shrinkM k IN O_poly 1
   shrinkM_steps_big_O   |- !k. stepsOf o combin$C shrinkM k IN big_O (\n. ulog n)
   shrinkM_thm           |- !n k. (valueOf (shrinkM n k) = n DIV 2 ** k) /\
                                  stepsOf o combin$C shrinkM k IN big_O (\n. ulog n)

   Integer Root Monad:
   rootM_def             |- !n k. rootM k n =
                                  do
                                    k0 <- zeroM k;
                                    n0 <- zeroM n;
                                    if k0 then unit (ROOT 0 n)
                                    else if n0 then 0c
                                    else
                                      do
                                        n' <- shrinkM n k;
                                        r <- rootM k n';
                                        x <- twiceM r;
                                        y <- incM x;
                                        z <- expM y k;
                                        b <- leqM z n;
                                        c <- boolM b;
                                        addM x c
                                      od
                                  od
#  rootM_value             |- !k n. valueOf (rootM k n) = ROOT k n
   rootM_steps_thm         |- !k n. (let r = ROOT k (n DIV 2 ** k) in
                                    stepsOf (rootM k n) =
                                      size k + size n +
                                      if k = 0 \/ n = 0 then 0
                                      else 1 + TWICE (size r) + TWICE (size (TWICE r)) +
                                           MAX (size ((TWICE r + 1) ** k)) (size n) +
                                           size ((TWICE r + 1) ** k - n) +
                                           stepsOf (shrinkM n k) +
                                           stepsOf (expM (TWICE r + 1) k) +
                                           stepsOf (rootM k (n DIV 2 ** k)))
   rootM_steps_k_0         |- !k. stepsOf (rootM k 0) = 1 + size k
   rootM_steps_0_n         |- !n. stepsOf (rootM 0 n) = 1 + size n
   rootM_steps_by_div_loop |- !k. (let body n = (let r = ROOT k (n DIV 2 ** k) in
                                         if k = 0 then 0
                                         else 1 + size k + size n + TWICE (size r) +
                                              TWICE (size (TWICE r)) +
                                              MAX (size ((TWICE r + 1) ** k)) (size n) +
                                              size ((TWICE r + 1) ** k - n) + stepsOf (shrinkM n k) +
                                              stepsOf (expM (TWICE r + 1) k))
                                    in !n. stepsOf (rootM k n) =
                                           if n = 0 then 1 + size k
                                           else body n + stepsOf (rootM k (n DIV 2 ** k)))
   rootM_body_upper    |- !k. (let body n = (let r = ROOT k (n DIV 2 ** k) in
                                      if k = 0 then 0
                                      else 1 + size k + size n + TWICE (size r) +
                                           TWICE (size (TWICE r)) +
                                           MAX (size ((TWICE r + 1) ** k)) (size n) +
                                           size ((TWICE r + 1) ** k - n) +
                                           stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
                                in !n. body n <= 3 + 4 * k + size k + 7 * size n +
                                                 5 * k * size k * size n +
                                                 135 * k ** 3 * size k ** 2 * size n ** 2)
   rootM_body_bound    |- !k. (let body n = (let r = ROOT k (n DIV 2 ** k) in
                                      if k = 0 then 0
                                      else 1 + size k + size n + TWICE (size r) +
                                           TWICE (size (TWICE r)) +
                                           MAX (size ((TWICE r + 1) ** k)) (size n) +
                                           size ((TWICE r + 1) ** k - n) +
                                           stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
                                in !n. body n <= 155 * k ** 3 * size k ** 2 * size n ** 2)
   rootM_steps_upper   |- !k n. stepsOf (rootM k n) <=
                                1 + size k + 3 * size n + 4 * k * size n + size k * size n +
                                7 * size n ** 2 + 5 * k * size k * size n ** 2 +
                                135 * k ** 3 * size k ** 2 * size n ** 3
   rootM_steps_bound   |- !k n. stepsOf (rootM k n) <= 157 * MAX 1 k ** 3 * size k ** 2 * size n ** 3
   rootM_steps_O_base  |- !n. stepsOf o combin$C rootM n IN big_O (POLY 1 o (\k. k ** 3 * size k ** 2 * size n ** 3))
   rootM_steps_O_poly  |- !k. stepsOf o rootM k IN O_poly 3
   rootM_steps_big_O   |- !k. stepsOf o rootM k IN big_O (\n. ulog n ** 3)
   rootM_thm           |- !k n. (valueOf (rootM k n) = ROOT k n) /\
                                stepsOf o rootM k IN big_O (\n. ulog n ** 3)

   Integer Square-root Monad:
   sqrtM_def           |- sqrtM = rootM 2
#  sqrtM_value         |- !n. valueOf (sqrtM n) = SQRT n
   sqrtM_steps_upper   |- !n. stepsOf (sqrtM n) <= 3 + 3 * size n + 8 * size n +
                              TWICE (size n) + 7 * size n ** 2 + 20 * size n ** 2 + 4320 * size n ** 3
   sqrtM_steps_bound   |- !n. stepsOf (sqrtM n) <= 5024 * size n ** 3
   sqrtM_steps_O_poly  |- stepsOf o sqrtM IN O_poly 3
   sqrtM_steps_big_O   |- stepsOf o sqrtM IN big_O (\n. ulog n ** 3)
   sqrtM_thm           |- !n. (valueOf (sqrtM n) = SQRT n) /\
                              stepsOf o sqrtM IN big_O (\n. ulog n ** 3)

   Power Free Monad:
   power_free_loopM_def    |- !n k. power_free_loopM n k =
                                    do
                                      k0 <- zeroM k;
                                      k1 <- oneM k;
                                      if k0 then unit T
                                      else if k1 then unit T
                                      else
                                        do
                                          r <- rootM k n;
                                          m <- expM r k;
                                          gd <- eqM m n;
                                          if gd then unit F
                                          else do k' <- decM k; power_free_loopM n k' od
                                        od
                                    od
   power_freeM_def         |- !n. power_freeM n =
                                  do
                                    m <- ulogM n;
                                    m0 <- zeroM m;
                                    if m0 then unit F else power_free_loopM n m
                                  od
#  power_free_loopM_value  |- !n k. valueOf (power_free_loopM n k) <=> n power_free_upto k
#  power_freeM_value       |- !n. valueOf (power_freeM n) <=> power_free_test n
   power_freeM_value_alt   |- !n. valueOf (power_freeM n) <=> power_free n
   power_freeM_steps_thm   |- !n. stepsOf (power_freeM n) =
                                  if n = 0 then 2
                                  else if n = 1 then 12
                                       else stepsOf (ulogM n) + size (ulog n) +
                                            stepsOf (power_free_loopM n (ulog n))

   power_free_loopM_steps_n_0  |- !n. stepsOf (power_free_loopM n 0) = 2
   power_free_loopM_steps_thm  |- !n k. stepsOf (power_free_loopM n k) =
                                        TWICE (size k) +
                                        if k = 0 \/ k = 1 then 0
                                        else size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                                             if ROOT k n ** k = n then 0
                                             else size k + stepsOf (power_free_loopM n (k - 1))
   power_free_loopM_steps_by_dec_loop
                               |- !n. (let eq k = ROOT k n ** k = n ;
                                           body k =
                                             if k <= 1 then 2
                                             else size n + TWICE (size k) + stepsOf (rootM k n) +
                                             stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
                                        in !k. stepsOf (power_free_loopM n k) =
                                               if k = 0 then 2
                                               else body k +
                                                    if eq k then 0
                                                    else stepsOf (power_free_loopM n (k - 1)))
   power_free_loopM_body_upper |- !n. (let eq k = ROOT k n ** k = n ;
                                           body k =
                                             if k <= 1 then 2
                                             else size n + TWICE (size k) + stepsOf (rootM k n) +
                                             stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
                                        in !k. body k <= size n + 3 * size k +
                                                 15 * k ** 3 * size k ** 2 * size n ** 2 +
                                                 157 * k ** 3 * size k ** 2 * size n ** 3)
   power_free_loopM_body_bound |- !n. (let eq k = ROOT k n ** k = n ;
                                           body k =
                                             if k <= 1 then 2
                                             else size n + TWICE (size k) + stepsOf (rootM k n) +
                                             stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
                                        in !k. body k <= 176 * MAX 1 k ** 3 * size k ** 2 * size n ** 3)
   power_free_loopM_steps_upper  |- !n k. stepsOf (power_free_loopM n k) <=
                                          2 + 176 * k ** 4 * size k ** 2 * size n ** 3
   power_free_loopM_steps_bound  |- !n k. stepsOf (power_free_loopM n k) <=
                                          178 * MAX 1 k ** 4 * size k ** 2 * size n ** 3
   power_free_loopM_steps_O_base |- !n. stepsOf o power_free_loopM n IN
                                        big_O (POLY 1 o (\k. k ** 4 * size k ** 2 * size n ** 3))
   power_freeM_steps_upper   |- !n. stepsOf (power_freeM n) <=
                                    11 + 9 * size n + 11 * size n ** 2 + 176 * size n ** 9
   power_freeM_steps_bound   |- !n. stepsOf (power_freeM n) <= 207 * size n ** 9
   power_freeM_steps_O_poly  |- stepsOf o power_freeM IN O_poly 9
   power_freeM_steps_big_O   |- stepsOf o power_freeM IN big_O (\n. ulog n ** 9)
   power_freeM_thm           |- !n. (valueOf (power_freeM n) <=> power_free n) /\
                                    stepsOf o power_freeM IN big_O (\n. ulog n ** 9)

   power_check_loopM_def   |- !n b. power_check_loopM b n =
                                    do
                                      b0 <- zeroM b;
                                      b1 <- oneM b;
                                      if b0 then unit F
                                      else if b1 then unit T
                                      else
                                        do
                                          gd <- power_ofM b n;
                                          if gd then unit F
                                          else do b' <- decM b; power_check_loopM b' n od
                                        od
                                    od
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
(* Fast Exponentiation (Repeated Squares Method)                             *)
(* ------------------------------------------------------------------------- *)
(* Fast Exponentiation -- recursive form.
   b ** n =
      if (n = 0) then return 1.
      let result = (b * b) ** (HALF n)
       in if EVEN n then return result
                    else return b * result
*)

(* Fast Exponentiation -- iterative form *)
(* Pseudocode: compute (m ** n)
   m ** n =
      r <- 1
      loop:
      if (n == 0) return r
      if (ODD n) r <- r * m
      n <- HALF n
      m <- SQ m
      goto loop
*)

(*
> EXP_EQN;
val it = |- !m n. m ** n =
                  if n = 0 then 1
                  else if EVEN n then SQ m ** HALF n
                  else m * SQ m ** HALF n: thm
*)

(* Define exponentiation in monadic style *)
Definition expM_def:
  expM b n =
      do
         gd <- zeroM n;
         if gd then return 1
         else do
                 b' <- sqM b;
                 n' <- halfM n;
                 r  <- expM b' n';
                 ifM (evenM n) (return r) (mulM b r);
              od
      od
Termination WF_REL_TAC `measure (λ(b,n). n)` >> simp[]
End

(*
> EVAL ``MAP (expM 2) [0 .. 10]``; =
         [(1,Count 1); (2,Count 13); (4,Count 34); (8,Count 40); (16,Count 77); (32,Count 87);
          (64,Count 92); (128,Count 106); (256,Count 183); (512,Count 201); (1024,Count 210)]
*)

(* Theorem: valueOf (expM b n) = b ** n *)
(* Proof: by induction from expM_ind_def, matching with EXP_EQN. *)
val expM_value = store_thm(
  "expM_value[simp]",
  ``!b n. valueOf (expM b n) = b ** n``,
  ho_match_mp_tac (theorem "expM_ind") >>
  rw[] >>
  rw[Once expM_def, Once EXP_EQN]);

(* Theorem: stepsOf (expM b n) =
            if n = 0 then 1
            else 1 + 5 * size n + (size b) ** 2 +
                 (if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))) +
                 stepsOf (expM (b * b) (HALF n)) *)
(* Proof:
     stepsOf (expM b n)
   = stepsOf (zeroM n) + if n = 0 then 0
     else stepsOf (sqM b) +
          stepsOf (halfM n) +
          stepsOf (expM (b * b) (HALF n)) +
          stepsOf (evenM n) +
          if EVEN n then stepsOf (return (b * b) ** (HALF n))
                    else stepsOf (mulM b (b * b) ** (HALF n))
   = size n + if n = 0 then 0
     else (size b) ** 2 +
          2 * (size n) +
          stepsOf (expM (b * b) (HALF n)) +
          2 * size n + 1 + if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))
  = if n = 0 then 1
    else (size b) ** 2 + 3 * (size n) +
          2 * size n + 1 + if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n))) +
          stepsOf (expM (b * b) (HALF n))
  = if n = 0 then 1
    else 1 + 5 * size n + (size b) ** 2 +
          (if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))) +
          stepsOf (expM (b * b) (HALF n))
*)
val expM_steps_thm = store_thm(
  "expM_steps_thm",
  ``!b n. stepsOf (expM b n) =
          if n = 0 then 1
          else 1 + 5 * size n + (size b) ** 2 +
               (if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))) +
               stepsOf (expM (b * b) (HALF n))``,
  rw[Once expM_def]);

(* Theorem: stepsOf (expM b 0) = 1 *)
(* Proof: by expM_steps_thm *)
val expM_steps_b_0 = store_thm(
  "expM_steps_b_0",
  ``!b. stepsOf (expM b 0) = 1``,
  rw[Once expM_steps_thm]);

(* Theorem: let body b n = 1 + 5 * size n + (size b) ** 2 +
                      if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))
            in !b n. stepsOf (expM b n) =
                     if n = 0 then 1 else body b n + stepsOf (expM (b * b) (HALF n)) *)
(* Proof:
     stepsOf (expM b n)
   = if n = 0 then 1
      else 1 + 5 * size n + (size b) ** 2 +
           (if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))) +
           stepsOf (expM (b * b) (HALF n))                 by expM_steps_thm
   = if n = 0 then 1 else body n + stepsOf (expM (b * b) (HALF n))
   where body n = 1 + 5 * size n + (size b) ** 2 +
           (if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n))))
*)
val expM_steps_by_sq_div_loop = store_thm(
  "expM_steps_by_sq_div_loop",
  ``let body b n = 1 + 5 * size n + (size b) ** 2 +
                   if EVEN n then 0 else (size b) * (size ((b * b) ** (HALF n)))
    in !b n. stepsOf (expM b n) =
             if n = 0 then 1 else body b n + stepsOf (expM (b * b) (HALF n))``,
  rw[Once expM_steps_thm]);

(* Alternate form of expM_steps_by_sq_div_loop *)
val expM_steps_by_sq_div_loop_alt = store_thm(
  "expM_steps_by_sq_div_loop_alt",
  ``let body b n = 1 + 5 * size n + (size b) ** 2 +
                  if EVEN n then 0 else (size b) * (size ((b ** 2) ** (HALF n)))
    in !b n. stepsOf (expM b n) =
             if n = 0 then 1 else body b n + stepsOf (expM (b ** 2) (HALF n))``,
  metis_tac[expM_steps_by_sq_div_loop, EXP_2]);

(*
This puts expM_steps in the category: halving loop with body cover, RISING SQ.
   expM_steps_by_sq_div_loop:
        !b n. loop b n = if n = 0 then quit b else body b n + loop (SQ b) (HALF n)
suitable for: loop2_div_rise_count_cover_le
*)

(* Theorem: stepsOf (expM b n) <=
            1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2 *)
(* Proof:
   Let loop = (\b n. stepsOf (expM b n)),
       body = (\b n. 1 + 5 * size n + (size b) ** 2 +
                  if EVEN n then 0 else size b * (size ((b * b) ** (HALF n)))),
       cover = (\b n. 1 + 5 * size n + (size b) ** 2 + size b * (size ((b * b) ** (HALF n)))),
       quit = (\b. 1).
   Then !b n. loop b n = if n = 0 then quit b else body b n + loop (SQ b) (HALF n)
                                              by expM_steps_by_sq_div_loop

   The result follows                         by loop2_div_rise_count_cover_le

   Note !x y. body x y <= cover x y
    and MONO2 cover                           by size_monotone_le, EXP_EXP_MULT, size_exp_base_le, size_exp_exp_le
    and RISING SQ                             by SELF_LE_SQ
   Thus loop b n <= 1 + pop 2 n * cover (FUNPOW SQ (pop 2 n) b) n
                                              by loop2_div_rise_count_cover_le
   Note the use of pop 2 size <= size n       by pop_size
        is not good here.
   Better use pop_2_size, with equality,
      and having n <> 0 to deal with (1 + n) and MAX (1 n).

   If n = 0, loop b n = 1, so trivially true.
   If n <> 0, then pop 2 n = size n           by pop_2_size, 0 < n
   Let k = FUNPOW SQ (size n) b.
   Thus loop b n <= 1 + size n * cover k n    by pop 2 n = size n

   Work out cover k n.
   Note k = FUNPOW SQ sn b = b ** (2 ** sn)   by FUNPOW_SQ
   Then size k <= 2 * (MAX 1 n) * size b      by size_exp_two_power_upper
                = 2 * n * size b              by 0 < n

        cover k n
      = 1 + 5 * size n + size k ** 2 + size k * size (SQ k ** HALF n)
      = 1 + 5 * size n + size k ** 2 + size k * size (k ** (2 * HALF n))   by EXP_EXP_MULT
     <= 1 + 5 * size n + size k ** 2 + size k * size (k ** n)              by TWO_HALF_LE_THM, size_exp_base_le
     <= 1 + 5 * size n + size k ** 2 + size k * (n * size k)               by size_exp_upper_alt, 0 < n
      = 1 + 5 * size n + size k ** 2 + n * size k ** 2                     by EXP_2
     <= 1 + 5 * size n + (1 + n) * size k ** 2
     <= 1 + 5 * size n + 2 * n * size k ** 2               by 1 <= n from 0 < n
     <= 1 + 5 * size n + 2 * n * (2 * n * size b) ** 2
      = 1 + 5 * size n + 8 * n ** 3 * size b ** 2

   Thus loop b n
     <= 1 + size n * (1 + 5 * size n + 8 * n ** 3 * size b ** 2)
      = 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2  by LEFT_ADD_DISTRIB
*)
val expM_steps_upper = store_thm(
  "expM_steps_upper",
  ``!b n. stepsOf (expM b n) <=
          1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2``,
  rpt strip_tac >>
  qabbrev_tac `loop = \b n. stepsOf (expM b n)` >>
  `loop b n <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2` suffices_by rw[Abbr`loop`] >>
  assume_tac expM_steps_by_sq_div_loop >>
  qabbrev_tac `body = \b n. 1 + 5 * size n + size b ** 2 + if EVEN n then 0 else size b * size (SQ b ** HALF n)` >>
  qabbrev_tac `cover = \b n. 1 + 5 * size n + (size b) ** 2 + size b * (size ((b * b) ** (HALF n)))` >>
  qabbrev_tac `f = \n. n * n` >>
  qabbrev_tac `quit = \b:num. 1` >>
  `!b n. loop b n = if n = 0 then quit b else body b n + loop (f b) (HALF n)` by metis_tac[] >>
  `1 < 2` by decide_tac >>
  `!x y. body x y <= cover x y` by rw[Abbr`body`, Abbr`cover`] >>
  `MONO2 cover` by
  (rw[Abbr`cover`, Abbr`f`] >>
  `size y1 <= size y2` by rw[size_monotone_le] >>
  `size x1 <= size x2` by rw[size_monotone_le] >>
  `size x1 ** 2 <= size x2 ** 2` by rw[size_monotone_le] >>
  `2 * HALF y1 <= 2 * HALF y2` by rw[HALF_LE_MONO] >>
  `size ((x1 ** 2) ** HALF y1) = size (x1 ** (2 * HALF y1))` by rw[EXP_EXP_MULT] >>
  `size ((x2 ** 2) ** HALF y2) = size (x2 ** (2 * HALF y2))` by rw[EXP_EXP_MULT] >>
  `size (x1 ** (2 * HALF y1)) <= size (x1 ** (2 * HALF y2))` by rw[size_exp_base_le] >>
  `size (x1 ** (2 * HALF y2)) <= size (x2 ** (2 * HALF y2))` by rw[size_exp_exp_le] >>
  `size x1 * size ((x1 ** 2) ** HALF y1) <= size x2 * size ((x2 ** 2) ** HALF y2)` by rw[LE_MONO_MULT2] >>
  decide_tac) >>
  `RISING f` by rw[SELF_LE_SQ, Abbr`f`] >>
  imp_res_tac loop2_div_rise_count_cover_le >>
  first_x_assum (qspecl_then [`n`, `b`] strip_assume_tac) >>
  Cases_on `n = 0` >| [
    `loop b n = 1` by metis_tac[] >>
    decide_tac,
    `0 < n` by decide_tac >>
    `pop 2 n = size n` by rw[pop_2_size] >>
    qabbrev_tac `k = FUNPOW f (size n) b` >>
    `loop b n <= 1 + size n * cover k n` by metis_tac[] >>
    `cover k n <= 1 + 5 * size n + 8 * n ** 3 * size b ** 2` by
  (rw[Abbr`cover`, Abbr`f`] >>
    `(k ** 2) ** HALF n = k ** (2 * HALF n)` by rw[EXP_EXP_MULT] >>
    `2 * HALF n <= n` by rw[TWO_HALF_LE_THM] >>
    `size (k ** TWICE (HALF n)) <= size (k ** n)` by rw[size_exp_base_le] >>
    `size (k ** n) <= n * size k` by rw[size_exp_upper_alt] >>
    `size k * size ((k ** 2) ** HALF n) <= size k * (n * size k)` by rw[] >>
    `size k * (n * size k) = n * size k ** 2` by rw[] >>
    `size k * size ((k ** 2) ** HALF n) + size k ** 2 <= (1 + n) * size k ** 2` by decide_tac >>
    `1 + n <= 2 * n` by decide_tac >>
    `(1 + n) * size k ** 2 <= 2 * n * size k ** 2` by rw[] >>
    `size k = size (b ** (2 ** size n))` by metis_tac[FUNPOW_SQ] >>
    `MAX 1 n = n` by rw[MAX_DEF] >>
    `size (b ** (2 ** size n)) <= 2 * n * size b` by metis_tac[size_exp_two_power_upper] >>
    `size k ** 2 <= (2 * n * size b) ** 2` by rw[] >>
    `n * size k ** 2 <= n * ((TWICE n * size b) ** 2)` by rw[] >>
    `n * (TWICE n * size b) ** 2 = n * (4 * n ** 2 * size b ** 2)` by rw[EXP_BASE_MULT] >>
    `_ = 4 * n ** 3 * size b ** 2` by rw[] >>
    decide_tac) >>
    `size n * cover k n <= size n * (1 + 5 * size n + 8 * n ** 3 * size b ** 2)` by rw[] >>
    `size n * (1 + 5 * size n + 8 * n ** 3 * size b ** 2) =
    size n + 5 * size n * size n + 8 * size n * n ** 3 * size b ** 2` by decide_tac >>
    `_ = size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2` by rw[] >>
    decide_tac
  ]);

(* Extract theorems *)
val expM_steps_0_upper = save_thm("expM_steps_0_upper",
    expM_steps_upper |> SPEC ``0`` |> SIMP_RULE (srw_ss()) []);
val expM_steps_1_upper = save_thm("expM_steps_1_upper",
    expM_steps_upper |> SPEC ``1`` |> SIMP_RULE (srw_ss()) []);
(*
val expM_steps_0_upper =
   |- !n. stepsOf (expM 0 n) <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3
val expM_steps_1_upper =
   |- !n. stepsOf (expM 1 n) <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3
*)

(* Theorem: stepsOf (expM b n) <= 15 * (MAX 1 n) ** 3 * size b ** 2 * size n ** 2 *)
(* Proof:
      stepsOf (expM b n)
   <= 1 + size n + 5 * size n ** 2 + 8 * size n * n ** 3 * size b ** 2  by expM_steps_upper
   <= (1 + 1 + 5 + 8) * size n ** 2 * n ** 3 * size b ** 2              by dominant term
    = 15 * n ** 3 * size n ** 2 * size b ** 2
   Use (MAX 1 n) to cater for n = 0.
*)
val expM_steps_bound = store_thm(
  "expM_steps_bound",
  ``!b n. stepsOf (expM b n) <= 15 * (MAX 1 n) ** 3 * size b ** 2 * size n ** 2``,
  rpt strip_tac >>
  assume_tac expM_steps_upper >>
  last_x_assum (qspecl_then [`b`, `n`] strip_assume_tac) >>
  qabbrev_tac `m = MAX 1 n` >>
  qabbrev_tac `t = m ** 3 * size b ** 2 * size n ** 2` >>
  `stepsOf (expM b n) <= 15 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ n <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size n <= t` by
  (`size n <= size n * (m ** 3 * size b ** 2 * size n)` by rw[MULT_POS] >>
  `size n * (m ** 3 * size b ** 2 * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size n ** 2 <= t` by
    (`size n ** 2 <= size n ** 2 * (m ** 3 * size b ** 2)` by rw[MULT_POS] >>
  `size n ** 2 * (m ** 3 * size b ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size n * n ** 3 * size b ** 2 <= t` by
      (`n ** 3 <= m ** 3` by rw[] >>
  `size n * n ** 3 * size b ** 2 <= m ** 3 * size n * size b ** 2` by rw[] >>
  `m ** 3 * size n * size b ** 2 <= m ** 3 * size n * size b ** 2 * (size n)` by rw[MULT_POS] >>
  `m ** 3 * size n * size b ** 2 * (size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: (stepsOf o expM b) IN big_O (POLY 1 o (\n. n ** 3 * size b ** 2 * size n ** 2)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?k c. !n. k < n ==> stepsOf (expM b n) <= c * n ** 3 * size b ** 2 * size n ** 2
   Note stepsOf (expM b n)
        <= 15 * (MAX 1 n) ** 3 * size b ** 2 * size n ** 2    by expM_steps_bound
   Take k = 0, c = 15.
   Then MAX 1 n = n       by MAX_DEF, 0 < n
   and the result follows.
*)
val expM_steps_O_base = store_thm(
  "expM_steps_O_base",
  ``!b. (stepsOf o expM b) IN big_O (POLY 1 o (\n. n ** 3 * size b ** 2 * size n ** 2))``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `15` >>
  rpt strip_tac >>
  `MAX 1 n = n` by rw[MAX_DEF] >>
  metis_tac[expM_steps_bound]);

(* Theorem: (stepsOf o expM b) IN big_O (POLY 1 o (\n. n ** 3 * (size n) ** 2)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?k c. !n. k < n ==> stepsOf (expM b n) <= c * n ** 3 * size b ** 2 * size n ** 2
   Note stepsOf (expM b n)
        <= 15 * (MAX 1 n) ** 3 * size b ** 2 * size n ** 2    by expM_steps_bound
   Take k = 0, c = 15.
   Then MAX 1 n = n       by MAX_DEF, 0 < n
   and the result follows.
   or, by expM_steps_O_base.
*)
val expM_steps_O_poly = store_thm(
  "expM_steps_O_poly",
  ``!b. (stepsOf o expM b) IN big_O (POLY 1 o (\n. n ** 3 * (size n) ** 2))``,
  rw[big_O_def, POLY_def] >>
  assume_tac expM_steps_bound >>
  first_x_assum (qspec_then `b` strip_assume_tac) >>
  qexists_tac `0` >>
  qexists_tac `15 * (size b) ** 2` >>
  rpt strip_tac >>
  `MAX 1 n = n` by rw[MAX_DEF] >>
  `15 * size b ** 2 * n ** 3 * size n ** 2 = 15 * n ** 3 * size b ** 2 * size n ** 2` by decide_tac >>
  metis_tac[]);

(* Theorem: (stepsOf o combin$C expM n) IN O_poly 2 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !b. h < b ==> stepsOf (expM b n) <= k * size b ** 2
   Note stepsOf (expM b n) <= 15 * MAX 1 n ** 3 * size b ** 2 * size n ** 2   by expM_steps_bound
   Take any h, say 0, k = 15 * MAX 1 n ** 3 * size n ** 2,
   The result follows.
*)
val expM_steps_O_swap = store_thm(
  "expM_steps_O_swap",
  ``!n. (stepsOf o combin$C expM n) IN O_poly 2``,
  rw[O_poly_thm] >>
  assume_tac expM_steps_bound >>
  qexists_tac `0` >>
  qexists_tac `15 * MAX 1 n ** 3 * size n ** 2` >>
  qx_gen_tac `b` >>
  rpt strip_tac >>
  last_x_assum (qspecl_then [`b`, `n`] strip_assume_tac) >>
  decide_tac);

(* Theorem: (stepsOf o expM b) IN big_O (\n. n ** 3 * (ulog n) ** 2) *)
(* Proof:
   Let 1 < n.
   Then MAX 1 n = n                      by MAX_DEF, 0 < n
    and ulog n <> 0                      by ulog_eq_0, n <> 0, n <> 1
   Note size n <= 1 + ulog n             by size_ulog
               <= ulog n + ulog n        by ulog n <> 0
                = 2 * ulog n

   Note (stepsOf (expM b n)
     <= 15 * MAX 1 n ** 3 * size b ** 2 * size n ** 2   by expM_steps_bound
     <= 15 * size b ** 2 * n ** 3 * size n ** 2         by MAX 1 n = n
     <= 15 * size b ** 2 * n ** 3 * (2 * ulog n) ** 2   by size n <= 2 * ulog n
      = 4 * 15 * size b ** 2 * n ** 3 * ulog n ** 2
   Thus (stepsOf o expM b) IN big_O (\n. n ** 3 * (ulog n) ** 2)
     by big_O_def, with 1 < n, and k = 60 * size b ** 2.
*)
val expM_steps_big_O = store_thm(
  "expM_steps_big_O",
  ``!b. (stepsOf o expM b) IN big_O (\n. n ** 3 * (ulog n) ** 2)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `60 * size b ** 2` >>
  rpt strip_tac >>
  `stepsOf (expM b n) <= 15 * MAX 1 n ** 3 * size b ** 2 * size n ** 2` by rw[expM_steps_bound] >>
  `MAX 1 n = n` by rw[MAX_DEF] >>
  `size n <= 1 + ulog n` by rw[size_ulog] >>
  `0 < ulog n` by fs[ulog_eq_0] >>
  `size n <= 2 * ulog n` by decide_tac >>
  `size n ** 2 <= (2 * ulog n) ** 2` by rw[] >>
  `(2 * ulog n) ** 2 = 4 * ulog n ** 2` by rw[EXP_BASE_MULT] >>
  `15 * MAX 1 n ** 3 * size b ** 2 * size n ** 2 =
    15 * size b ** 2 * n ** 3 * size n ** 2` by rw[] >>
  `size b ** 2 * n ** 3 * size n ** 2 <=
    size b ** 2 * n ** 3 * (4 * ulog n ** 2)` by rw[MULT_POS] >>
  decide_tac);

(* Theorem: (valueOf (expM b n) = b ** n) /\
            (stepsOf o expM b) IN big_O (\n. n ** 3 * (ulog n) ** 2) *)
(* Proof: by expM_value, expM_steps_big_O *)
val expM_thm = store_thm(
  "expM_thm",
  ``!b n. (valueOf (expM b n) = b ** n) /\
         (stepsOf o expM b) IN big_O (\n. n ** 3 * (ulog n) ** 2)``,
  metis_tac[expM_value, expM_steps_big_O]);

(* ------------------------------------------------------------------------- *)
(* Root Extraction                                                           *)
(* ------------------------------------------------------------------------- *)
(* Root computation:

say, to compute cube root of 125.
chopping factor = 8 = 2 ** 3 for ROOT 3 n.
The chopping list:
EVAL ``size 125``;
|- size 125 = 7

EVAL ``GENLIST (\j. 125 DIV (8 ** j)) (2 + (size 25) DIV 3)``;
|- GENLIST (\j. 125 DIV 8 ** j) (2 + size 25 DIV 3) = [125; 15; 1]

Then maintain two variables
 step     z (start with 0)     x (to be popped from chopping list)
 ------------------------------------------------
 TWICE z    0                  1  from pop
 test: (z + 1) ** 3 <= 1 ? or 1 ** 3 <= 1 ? yes, z++
            1                  1
 next:      2                 15
 test: (z + 1) ** 3 <= 15 ? or 3 ** 3 <= 15 ? no, z
            2                 15
 next:      4                125
 test: (z + 1) ** 3 <= 125 ? or 5 ** 3 <= 125 ? yes, z++
            5                125
 next: no more, z = 5 is the answer or 5 = cube root of 125.
*)

(* Define shrink: n shrink k = n DIV 2 ** k *)
(* Pseudocode: compute (n shrink k, halving of n k )
   n shrink k =
      loop:
      if (k == 0) return n
      n <- HALF n
      k <- DEC k
      goto loop
*)
Definition shrinkM_def:
  shrinkM n k =
       do
          gd <- zeroM k;
          if gd then return n
          else do
                  n' <- halfM n;
                  k' <- decM k;
                  shrinkM n' k'
               od
       od
Termination WF_REL_TAC `measure (λ(n,k). k)` >> simp[]
End
(* Note: this is better or faster than:
   computing (2 ** k), then perform n DIV (2 ** k).
*)

(*
> EVAL ``shrinkM 10 2``; = (2,Count 21): thm
> EVAL ``shrinkM 10 4``; = (0,Count 37): thm
*)

(* Theorem: valueOf (shrinkM n k) = n DIV (2 ** k) *)
(* Proof:
   By induction on k.
   Base: !n. valueOf (shrinkM n 0) = n DIV (2 ** 0)
         valueOf (shrinkM n 0)
       = valueOf (unit n)               by shrinkM_def
       = n                              by unit_value
       = n DIV 2 ** 0                   by EXP_0, DIV_ONE
   Step: !n. valueOf (shrinkM n k) = n DIV (2 ** k) ==>
         !n. valueOf (shrinkM n (SUC k)) = n DIV (2 ** (SUC k))
         valueOf (shrinkM n (SUC k))
       = valueOf (shrinkM (HALF n) k)   by shrinkM_def, SUC k <> 0
       = (HALF n) DIV (2 ** k)          by induction hypothesis
       = n DIV 2 ** (SUC k)             by HALF_DIV_TWO_POWER
*)
val shrinkM_value = store_thm(
  "shrinkM_value[simp]",
  ``!n k. valueOf (shrinkM n k) = n DIV (2 ** k)``,
  ho_match_mp_tac (theorem "shrinkM_ind") >>
  rw[] >>
  rw[Once shrinkM_def] >>
  `SUC (k - 1) = k` by decide_tac >>
  rw[HALF_DIV_TWO_POWER]);

(* Theorem: stepsOf (shrinkM n k) =
            size k +
            if k = 0 then 0
            else 2 * size n + size k + stepsOf (shrinkM (HALF n) (k - 1)) *)
(* Proof:
     stepsOf (shrinkM n k)
   = stepsOf (zeroM k) +
     if (k = 0) then stepsOf (unit n)
     else stepsOf (halfM n) + stepsOf (decM k) + stepsOf (shrinkM (HALF n) (k - 1))  by shrinkM_def
   = size k + if k = 0 then 0
     else 2 * size n + size k + stepsOf (shrinkM (HALF n) (k - 1))
*)
val shrinkM_steps_thm = store_thm(
  "shrinkM_steps_thm",
  ``!n k. stepsOf (shrinkM n k) =
          size k +
          if k = 0 then 0
          else 2 * size n + size k + stepsOf (shrinkM (HALF n) (k - 1))``,
  rw[Once shrinkM_def]);

(* Theorem: stepsOf (shrinkM n 0) = 1 *)
(* Proof:
      stepsOf (shrinkM n 0)
    = size 0 = 1             by shrinkM_steps_thm, size_0
*)
val shrinkM_steps_0 = store_thm(
  "shrinkM_steps_0",
  ``!n. stepsOf (shrinkM n 0) = 1``,
  rw[Once shrinkM_steps_thm]);

(* Theorem: stepsOf (shrinkM n 1) = 3 + 2 * size n *)
(* Proof:
      stepsOf (shrinkM n 1)
    = size 1 + 2 * (size n) + size 1 + stepsOf (shrinkM 0 (HALF n)) by shrinkM_steps_thm
    = 1 + 2 * size n + 1 + 1           by shrinkM_steps_0
    = 3 + 2 * size n                   by arithmetic
*)
val shrinkM_steps_1 = store_thm(
  "shrinkM_steps_1",
  ``!n. stepsOf (shrinkM n 1) = 3 + 2 * size n``,
  rw[Once shrinkM_steps_thm, shrinkM_steps_0]);

(* Theorem: stepsOf (shrinkM n k) =
            if k = 0 then 1
            else 2 * size k + 2 * size n + stepsOf (shrinkM (HALF n) (k - 1)) *)
(* Proof:
     stepsOf (shrinkM n k)
   = size k + if k = 0 then 0 else 2 * size n + size k + stepsOf (shrinkM (HALF n) (k - 1))
                                       by shrinkM_steps_thm
   = if k = 0 then size k
     else size k + 2 * size n + size k + stepsOf (shrinkM (HALF n) (k - 1))
   = if k = 0 then size 0              and size 0 = 1 by size_0
     else 2 * size k + 2 * size n + stepsOf (shrinkM (HALF n) (k - 1))
*)
val shrinkM_steps_by_half_dec_loop = store_thm(
  "shrinkM_steps_by_half_dec_loop",
  ``!n k. stepsOf (shrinkM n k) =
          if k = 0 then 1
          else 2 * size k + 2 * size n + stepsOf (shrinkM (HALF n) (k - 1))``,
  rw[Once shrinkM_steps_thm]);

(*
This puts shrinkM_steps in the category: dividing loop with body cover and transform.
   shrinkM_steps_by_half_dec_loop:
        !n k. loop n k = if k = 0 then quit n else body n k + loop (HALF n) (k - 1)
suitable for: loop2_dec_fall_count_le
*)

(* Theorem: stepsOf (shrinkM n k) <= 1 + 2 * k * size k + 2 * k * size n *)
(* Proof:
   Let loop = (\n k. stepsOf (shrinkM n k)),
       body = (\n k. 2 * size k + 2 * size n),
       quit = (\n. 1).
   Then loop n k = if k = 0 then quit n else body n k + loop (HALF n) (k - 1)
                                        by shrinkM_steps_by_half_dec_loop
    Now MONO2 body                      by size_monotone_le
    and FALLING HALF                    by HALF_LE
   Thus loop n k
     <= quit (FUNPOW f (hop 1 y) x) + hop 1 k * body n k   by loop2_dec_fall_count_le
      = 1 + k * (2 * size k + 2 * size n)                  by hop_1_n
      = 1 + 2 * k * size k + 2 * k * size n
*)
val shrinkM_steps_upper = store_thm(
  "shrinkM_steps_upper",
  ``!n k. stepsOf (shrinkM n k) <= 1 + 2 * k * size k + 2 * k * size n``,
  rpt strip_tac >>
  qabbrev_tac `loop = \n k. stepsOf (shrinkM n k)` >>
  qabbrev_tac `body = \n k. 2 * size k + 2 * size n` >>
  qabbrev_tac `f = \n. HALF n` >>
  qabbrev_tac `quit = \n:num. 1` >>
  `loop n k <= 1 + 2 * k * size k + 2 * k * size n` suffices_by rw[Abbr`loop`] >>
  assume_tac shrinkM_steps_by_half_dec_loop >>
  `!n k. loop n k = if k = 0 then quit n else body n k + loop (f n) (k - 1)` by metis_tac[] >>
  `MONO2 body` by
  (rw[Abbr`body`] >>
  `size x1 <= size x2` by rw[size_monotone_le] >>
  `size y1 <= size y2` by rw[size_monotone_le] >>
  decide_tac) >>
  `FALLING f` by rw[HALF_LE, Abbr`f`] >>
  `0 < 1` by decide_tac >>
  imp_res_tac loop2_dec_fall_count_le >>
  `loop n k <= 1 + k * body n k` by metis_tac[hop_1_n] >>
  `k * body n k = k * (2 * size k + 2 * size n)` by rw[Abbr`body`] >>
  `_ = 2 * k * size k + 2 * k * size n` by decide_tac >>
  decide_tac);

(* Theorem: stepsOf (shrinkM n k) <= 5 * MAX 1 k * size k * size n *)
(* Proof:
      stepsOf (shrinkM n k)
   <= 1 + 2 * k * size k + 2 * k * size n   by shrinkM_steps_upper
   <= (1 + 2 + 2) * k * size k * size n     by dominant term
    = 5 * k * size k * size n
   Use (MAX 1 k) to cater for k = 0.
*)
val shrinkM_steps_bound = store_thm(
  "shrinkM_steps_bound",
  ``!n k. stepsOf (shrinkM n k) <= 5 * MAX 1 k * size k * size n``,
  rpt strip_tac >>
  assume_tac shrinkM_steps_upper >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * size k * size n` >>
  `stepsOf (shrinkM n k) <= 5 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k * size k <= t` by
  (`k * size k <= m * size k` by rw[] >>
  `m * size k <= m * size k * size n` by rw[MULT_POS] >>
  `m * size k * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size n <= t` by
    (`k * size n <= m * size n` by rw[] >>
  `m * size n <= m * size n * size k` by rw[MULT_POS] >>
  `m * size n * size k = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: (stepsOf o (combin$C shrinkM) k) IN big_O (POLY 1 o (\n. (MAX 1 k) * size k * size n)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?h c. !n. h < n ==> stepsOf (shrinkM n k) <= c * size k * size n * MAX 1 k
   Note !n. stepsOf (shrinkM n k) <= 5 * MAX 1 k * size k * size n   by shrinkM_steps_bound
   Take h = 0, c = 5, the result follows.
*)
val shrinkM_steps_O_base = store_thm(
  "shrinkM_steps_O_base",
  ``!k. (stepsOf o (combin$C shrinkM) k) IN big_O (POLY 1 o (\n. (MAX 1 k) * size k * size n))``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `5` >>
  rpt strip_tac >>
  assume_tac shrinkM_steps_bound >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  decide_tac);

(* Theorem: (stepsOf o (combin$C shrinkM) k) IN O_poly 1 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k'. !n. h < n ==> stepsOf (shrinkM n k) <= k' * size n
   Note !n. stepsOf (shrinkM n k) <= 5 * MAX 1 k * size k * size n   by shrinkM_steps_bound
   Take any h, k' = 5 * MAX 1 k * size k, the result follows.
*)
val shrinkM_steps_O_poly = store_thm(
  "shrinkM_steps_O_poly",
  ``!k. (stepsOf o (combin$C shrinkM) k) IN O_poly 1``,
  rw[O_poly_thm] >>
  metis_tac[shrinkM_steps_bound]);

(* Theorem: (stepsOf o (combin$C shrinkM) k) IN big_O (\n. (ulog n)) *)
(* Proof:
   Note (stepsOf o (combin$C shrinkM) k) IN O_poly 1     by shrinkM_steps_O_poly
    and O_poly 1
      = big_O (POLY 1 o ulog)             by O_poly_eq_O_poly_ulog
      = (\n. ulog n)                      by POLY_def, FUN_EQ_THM
   The result follows.
*)
val shrinkM_steps_big_O = store_thm(
  "shrinkM_steps_big_O",
  ``!k. (stepsOf o (combin$C shrinkM) k) IN big_O (\n. (ulog n))``,
  assume_tac shrinkM_steps_O_poly >>
  `O_poly 1 = big_O (POLY 1 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 1 o ulog = \n. ulog n` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (shrinkM n k) = n DIV 2 ** k) /\
            (stepsOf o (combin$C shrinkM) k) IN big_O (\n. (ulog n)) *)
(* Proof: vy shrinkM_value, shrinkM_steps_big_O *)
val shrinkM_thm = store_thm(
  "shrinkM_thm",
  ``!n k. (valueOf (shrinkM n k) = n DIV 2 ** k) /\
         (stepsOf o (combin$C shrinkM) k) IN big_O (\n. (ulog n))``,
  metis_tac[shrinkM_value, shrinkM_steps_big_O]);

(* ------------------------------------------------------------------------- *)
(* Integer Root in Monadic Style                                             *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode: compute (ROOT k n), k-th root of n.

Make use of this root-power indentity: n^(1/k) = 2 (n / 2^k)^(1/k)
    ROOT k n =
       if k = 0 then (ROOT 0 n).               // for termination
       if n = 0 then 0.                        // for termination
       let x = 2 * k-th root of (n DIV (2 ** k))  // estimate
        in if n < (SUC x) ** k then x else (SUC x) // check
*)

(*
> ROOT_EQN |> SPEC ``k:num``;
val it = |- !n. 0 < k ==>
          ROOT k n =
          (let m = TWICE (ROOT k (n DIV 2 ** k))
            in m + if (m + 1) ** k <= n then 1 else 0): thm
*)

(* Define root in monadic style *)
Definition rootM_def:
  rootM k n =
       do
          k0 <- zeroM k;
          n0 <- zeroM n;
          if k0 then return (ROOT 0 n)
          else if n0 then return 0
          else do
                 n' <- shrinkM n k;
                 r  <- rootM k n';
                 x  <- twiceM r;
                 y  <- incM x;
                 z  <- expM y k;
                 b  <- leqM z n;
                 c  <- boolM b;
                 addM x c;
               od
       od
Termination WF_REL_TAC `measure (λ(k,n). n)` >> rw[] >>
            `1 < 2 ** k` by rw[ONE_LT_EXP] >> rw[DIV_LESS]
End

(*
> EVAL ``MAP (rootM 3) [0 .. 10]``; =
      [(0,Count 3); (1,Count 52); (1,Count 56); (1,Count 56); (1,Count 62); (1,Count 62);
       (1,Count 62); (1,Count 62); (2,Count 154); (2,Count 154); (2,Count 154)]: thm
*)

(* Theorem: valueOf (rootM k n) = ROOT k n *)
(* Proof:
   By induction from rootM_def, this is to show:
   (1) k <> 0 ==> 0 = ROOT k 0, true    by ROOT_OF_0
   (2) k <> 0 /\ n <> 0 ==> 2 * (ROOT k (n DIV 2 ** k)) +
       (if (2 * (ROOT k (n DIV 2 ** k)) + 1) ** k <= n then 1 else 0) = ROOT k n
       This is true                     by ROOT_EQN
*)
val rootM_value = store_thm(
  "rootM_value[simp]",
  ``!k n. valueOf (rootM k n) = ROOT k n``,
  ho_match_mp_tac (theorem "rootM_ind") >>
  rw[] >>
  rw[Once rootM_def] >>
  assume_tac ROOT_EQN >>
  last_x_assum (qspecl_then [`k`, `n`] strip_assume_tac) >>
  fs[]);

(* Theorem: let r = ROOT k (n DIV (2 ** k)) in
      stepsOf (rootM k n) =
      size k + size n +
      if (k = 0) \/ (n = 0) then 0
      else 1 + 2 * size r + 2 * size (2 * r) +
           MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
           stepsOf (shrinkM n k) +
           stepsOf (expM (2 * r + 1) k) +
           stepsOf (rootM k (n DIV (2 ** k))) *)
(* Proof:
   By rootM_def,
     stepsOf (rootM k n)
   = stepsOf (zeroM k) + stepsOf (zeroM n) +
     if (k = 0) \/ (n = 0) then 0
     else stepsOf (shrinkM n k) +
          stepsOf (rootM k (n DIV (2 ** k))) +
          stepsOf (twiceM (ROOT k (n DIV (2 ** k)))) +
          stepsOf (incM (2 * ROOT k (n DIV (2 ** k)))) +
          stepsOf (expM (2 * ROOT k (n DIV (2 ** k)) + 1) k) +
          stepsOf (leqM ((2 * ROOT k (n DIV (2 ** k)) + 1) ** k) n) +
          stepsOf (boolM (((2 * ROOT k (n DIV (2 ** k)) + 1) ** k) <= n)) +
          stepsOf (addM (2 * ROOT k (n DIV (2 ** k))) (if ... then 1 else 0))
   = size k + size n +
     if (k = 0) \/ (n = 0) then 0
     else stepsOf (shrinkM n k) +
          stepsOf (rootM k (n DIV (2 ** k))) +
          2 * size r +
          size (2 * r) +
          stepsOf (expM (2 * r + 1) k) +
          stepsOf (leqM ((2 * r + 1) ** k) n) +
          1 + MAX (size (2 * r)) (size 1 or size 0)   where r = ROOT k (n DIV (2 ** k))
   = size k + size n +
     if (k = 0) \/ (n = 0) then 0
     else stepsOf (shrinkM n k) +
          stepsOf (rootM k (n DIV (2 ** k))) +
          2 * size r +
          size (2 * r) +
          stepsOf (expM (2 * r + 1) k) +
          MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
          1 + size (2 * r)
   = size k + size n + if (k = 0) \/ (n = 0) then 0
     else 1 + 2 * size r + 2 * size (2 * r) +
          MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
          stepsOf (shrinkM n k) +
          stepsOf (expM (2 * r + 1) k) +
          stepsOf (rootM k (n DIV (2 ** k)))
*)
val rootM_steps_thm = store_thm(
  "rootM_steps_thm",
  ``!k n. let r = ROOT k (n DIV (2 ** k)) in
         stepsOf (rootM k n) =
         size k + size n +
         if (k = 0) \/ (n = 0) then 0
         else 1 + 2 * size r + 2 * size (2 * r) +
              MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
              stepsOf (shrinkM n k) +
              stepsOf (expM (2 * r + 1) k) +
              stepsOf (rootM k (n DIV (2 ** k)))``,
  (rw[Once rootM_def] >> fs[]) >>
  qabbrev_tac `r = ROOT k (n DIV 2 ** k)` >>
  `size (if (TWICE r + 1) ** k <= n then 1 else 0) = 1` by
  ((Cases_on `(TWICE r + 1) ** k <= n` >> rw[])) >>
  qabbrev_tac `t = size (if (TWICE r + 1) ** k <= n then 1 else 0)` >>
  `MAX (size (TWICE r)) t = size (2 * r)` by metis_tac[max_1_size_n, MAX_COMM] >>
  simp[]);

(* Theorem: stepsOf (rootM 0 n) = 1 + size k *)
(* Proof:
     stepsOf (rootM k 0)
   = size k + size 0 + 0       by rootM_steps_thm
   = 1 + size k                by size_0
*)
val rootM_steps_k_0 = store_thm(
  "rootM_steps_k_0",
  ``!k. stepsOf (rootM k 0) = 1 + size k``,
  rpt strip_tac >>
  `stepsOf (rootM k 0) = size k + size 0 + 0` by metis_tac[rootM_steps_thm] >>
  rw[]);

(* Theorem: stepsOf (rootM 0 n) = 1 + size n *)
(* Proof:
     stepsOf (rootM 0 n)
   = size 0 + size n + 0       by rootM_steps_thm
   = 1 + size n                by size_0
*)
val rootM_steps_0_n = store_thm(
  "rootM_steps_0_n",
  ``!n. stepsOf (rootM 0 n) = 1 + size n``,
  rpt strip_tac >>
  `stepsOf (rootM 0 n) = size 0 + size n + 0` by metis_tac[rootM_steps_thm] >>
  rw[]);

(* Theorem: let body n = let r = ROOT k (n DIV (2 ** k)) in
                if k = 0 then 0
                else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                    MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                    stepsOf (shrinkM n k) +
                    stepsOf (expM (2 * r + 1) k)
            in !n. stepsOf (rootM k n) = if n = 0 then 1 + size k
                   else body n + stepsOf (rootM k (n DIV (2 ** k))) *)
(* Proof:
     stepsOf (rootM k n)
   = size k + size n + if (k = 0) \/ (n = 0) then 0
     else 1 + 2 * size r + 2 * size (2 * r) +
          MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
          stepsOf (shrinkM n k) +
          stepsOf (expM (2 * r + 1) k) +
          stepsOf (rootM k (n DIV (2 ** k)))    by rootM_steps_thm
   = if (k = 0) \/ (n = 0) then size k + size n
     else size k + size n + 1 + 2 * size r + 2 * size (2 * r) +
          MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
          stepsOf (shrinkM n k) +
          stepsOf (expM (2 * r + 1) k) +
          stepsOf (rootM k (n DIV (2 ** k)))
   = if (n = 0) then 1 + size k
     else if (k = 0) then 1 + size n
     else size k + size n + 1 + 2 * size r + 2 * size (2 * r) +
          MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
          stepsOf (shrinkM n k) +
          stepsOf (expM (2 * r + 1) k) +
          stepsOf (rootM k (n DIV (2 ** k)))
   = if (n = 0) then 1 + size k
     else (if (k = 0) then 0
          else size k + size n + 1 + 2 * size r + 2 * size (2 * r) +
               MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
               stepsOf (shrinkM n k) +
               stepsOf (expM (2 * r + 1) k)) +
               stepsOf (rootM k (n DIV (2 ** k)))
        it just happens that when k = 0,
           stepsOf (rootM 0 (n DIV (2 ** 0)))
         = stepsOf (rootM 0 (n DIV 1))    by EXP_0
         = stepsOf (rootM 0 n)            by DIV_1
         = 1 + size n                     by rootM_steps_0_n
*)
val rootM_steps_by_div_loop = store_thm(
  "rootM_steps_by_div_loop",
  ``!k. let body n = let r = ROOT k (n DIV (2 ** k)) in
               if k = 0 then 0
               else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                    MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                    stepsOf (shrinkM n k) +
                    stepsOf (expM (2 * r + 1) k)
       in !n. stepsOf (rootM k n) =
              if n = 0 then 1 + size k
              else body n + stepsOf (rootM k (n DIV (2 ** k)))``,
  rw[] >>
  (Cases_on `n = 0` >> simp[]) >-
  rw[rootM_steps_k_0] >>
  assume_tac rootM_steps_thm >>
  last_x_assum (qspecl_then [`k`, `n`] strip_assume_tac) >>
  qabbrev_tac `r = ROOT k (n DIV 2 ** k)` >>
  `stepsOf (rootM k n) = size k + size n + if k = 0 \/ n = 0 then 0
      else 1 + TWICE (size r) + TWICE (size (TWICE r)) +
           MAX (size ((TWICE r + 1) ** k)) (size n) +
           size ((TWICE r + 1) ** k - n) + stepsOf (shrinkM n k) +
           stepsOf (expM (TWICE r + 1) k) +
           stepsOf (rootM k (n DIV 2 ** k))` by metis_tac[] >>
  (Cases_on `k = 0 \/ n = 0` >> simp[]) >>
  fs[rootM_steps_0_n]);

(*
This puts rootM_steps in the category: dividing loop with body cover.
   rootM_steps_by_div_loop:
        !n. loop n = if n = 0 then c else body n + loop (n DIV (2 ** k))
suitable for: loop_div_count_cover_le
*)

(* First, work out a cover for the complicated body. *)

(* Theorem: let body n = (let r = ROOT k (n DIV 2 ** k) in
            if k = 0 then 0
            else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                 MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                 stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
          in !n. body n <= 3 + 4 * k + size k + 7 * size n + 5 * k * size k * size n + 135 * k ** 3 * size k ** 2 * size n ** 2 *)
(* Proof:
   Let b = 2 * r + 1.
   If k = 0, this is trivial.
   If k <> 0,
   Let x = 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
           MAX (size (b ** k)) (size n) + size (b ** k - n),
       y = stepsOf (shrinkM n k),
       z = stepsOf (expM b k).

   Claim: r <= n
   Proof: Note 0 < 2 ** k                             by EXP_POS, 0 < 2
            so n DIV (2 ** k) <= n                    by DIV_LESS_EQ, 0 < 2 ** k
           ==> ROOT k (n DIV (2 ** k)) <= ROOT k n    by ROOT_LE_MONO, 0 < k
            or r <= ROOT k n                          by notation
           and ROOT k n <= n                          by ROOT_LE_SELF, 0 < k
          Thus r <= n.

   Claim: x <= 3 + 4 * k + size k + 7 * size n.
   Proof: If r = 0,
             Then b = 1.
             x = 1 + size k + size n + 2 * size 0 + 2 * size (2 * 0) +
                 MAX (size (1 ** k)) (size n) + size (1 ** k - n)
               = 1 + size k + size n + 2 + 2 + size n + 1      by size_0, size_1, max_1_size_n
               = 6 + size k + 2 * size n
              <= 2 + 4 * k + size k + 2 * size n      by 0 < k, or 1 <= k.
              <= 3 + 4 * k + size k + 7 * size n.
          If r <> 0, in several parts.
             Note b = 2 * r + 1
                    < 2 * r + 2 * r               by 0 < r
                    = 4 * r = r * 2 ** 2          by 4 = 2 ** 2
               or b < r * 2 ** 2.

      Claim: b ** k < n * 2 ** (2 * k)
      Proof:    b ** k
             <= (r * 2 ** 2) ** k                 by EXP_EXP_LE_MONO, b <= r * 2 ** 2
              = r ** k * (2 ** 2) ** k            by EXP_BASE_MULT
            But r ** k <= n DIV (2 ** k)          by ROOT
                        < n                       by DIV_LESS, ONE_LT_EXP
             so r ** k * (2 ** (2 * k)) < n * 2 ** (2 * k)       by above
            The result follows.

       Also 1 < 2 ** (2 * k)                      by ONE_LT_EXP, k <> 0
         so n < n * 2 ** (2 * k)                  by 0 < n, from 0 < r, r <= n
        and MAX (size (b ** k)) (size n)
          = size (MAX (b ** k) n)                 by size_max
         <= size (n * 2 ** (2 * k))               by MAX_LT, size_monotone_le
         <= size n + 2 * k                        by size_mult_two_power_upper

       Note size (b ** k - n)
         <= size (b ** k)                         by size_monotone_le
         <= size (n * 2 ** (2 * k))               by claim
         <= size n + 2 * k                        by size_mult_two_power_upper

       Note size r <= size n                      by size_monotone_le
        and size (2 * r) <= size (2 * n)          by size_monotone_le

       Finally,
            x = 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                MAX (size (b ** k)) (size n) + size (b ** k - n)
             <= 1 + size k + size n + 2 * size n + 2 * size (2 * n) + 2 * (size n + 2 * k)
              = 1 + size k + size n + 2 * size n + 2 * (size n + 1) + 2 * (size n + 2 * k)  by size_twice, n <> 0
              = 3 + 4 * k + size k + 7 * size n
              = 3 + 4k + sk + 7sn

   Note y <= 5 * MAX 1 k * size k * size n        by shrinkM_steps_bound, better than shrinkM_steps_upper
           = 5 * k * sk * sn                      by MAX 1 k = k, 0 < k

   Note z <= 15 * MAX 1 k ** 3 * size b ** 2 * size k ** 2  by expM_steps_bound, better than expM_steps_upper
           = 15 * (k ** 3) * size b ** 2 * sk ** 2

      Note 2 * r <= 2 * n                  by r <= n
      Thus b = 2 * r + 1
             < 2 * r + 2 * r = 4 * r       by r <> 0, or 1 <= r
        so b <= r * 2 ** 2.

       Now b < r * 2 ** 2 <= n * 2 ** 2    by r <= n
        so size b <= size (n * 2 ** 2)     by size_monotone_le
                  <= 2 + size n            by size_mult_two_power_upper
                  <= 2 * sn + sn = 3 sn    by size_pos
      Thus z <= 15 * k ** 3 * (3 sn) ** 2 * sk ** 2
             <= 135 * k ** 3 * sn ** 2 * sk ** 2

   Overall, x + y + z <= 3 + 4k + sk + 7sn + 5 k sk sn + 135 * k ** 3 * sn ** 2 * sk ** 2
*)
val rootM_body_upper = store_thm(
  "rootM_body_upper",
  ``!k. let body n = (let r = ROOT k (n DIV 2 ** k) in
            if k = 0 then 0
            else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                 MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                 stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
        in !n. body n <=
               3 + 4 * k + size k + 7 * size n + 5 * k * size k * size n + 135 * k ** 3 * size k ** 2 * size n ** 2``,
  rw_tac std_ss[] >>
  rw_tac bool_ss[Abbr`body`] >>
  qabbrev_tac `b = 2 * r + 1` >>
  (Cases_on `k = 0` >> rw_tac bool_ss[]) >-
  decide_tac >>
  qabbrev_tac `x = 1 + size k + size n + 2 * size r + 2 * (size (2 * r)) +
                    MAX (size (b ** k)) (size n) + size (b ** k - n)` >>
  qabbrev_tac `y = stepsOf (shrinkM n k)` >>
  qabbrev_tac `z = stepsOf (expM b k)` >>
  `r <= n` by
  (rw[Abbr`r`] >>
  `n DIV (2 ** k) <= n` by rw[DIV_LESS_EQ] >>
  `ROOT k (n DIV 2 ** k) <= ROOT k n` by rw[ROOT_LE_MONO] >>
  `ROOT k n <= n` by rw[ROOT_LE_SELF] >>
  decide_tac) >>
  `MAX 1 k = k` by rw[MAX_DEF] >>
  `y <= 5 * k * size k * size n` by metis_tac[shrinkM_steps_bound] >>
  `x <= 3 + 4 * k + size k + 7 * size n` by
    (Cases_on `r = 0` >| [
    `b = 1` by rw[Abbr`b`] >>
    `x = 5 + size k + 2 * size n + size (1 - n)` by rw[GSYM max_1_size_n, Abbr`x`] >>
    `size (1 - n) <= size 1` by rw[size_monotone_le] >>
    `size 1 = 1` by rw[] >>
    decide_tac,
    `b <= r * 2 ** 2` by rw[Abbr`b`] >>
    qabbrev_tac `t = 2 ** (2 * k)` >>
    `b ** k < n * t` by
  (`b ** k <= (r * 2 ** 2) ** k` by rw[EXP_EXP_LE_MONO] >>
    `(r * 2 ** 2) ** k = r ** k * (2 ** 2) ** k` by rw[EXP_BASE_MULT] >>
    `_ = r ** k * t` by rw[GSYM EXP_EXP_MULT, Abbr`t`] >>
    `r ** k <= n DIV (2 ** k)` by rw[ROOT, Abbr`r`] >>
    `n DIV (2 ** k) < n` by rw[DIV_LESS, ONE_LT_EXP] >>
    `r ** k * t < n * t` by rw[Abbr`t`] >>
    decide_tac) >>
    `MAX (size (b ** k)) (size n) <= size (n * t)` by
    (`1 < t` by rw[ONE_LT_EXP, Abbr`t`] >>
    `n < n * t` by rw[] >>
    `MAX (b ** k) n < n * t` by rw[MAX_LT] >>
    `MAX (size (b ** k)) (size n) = size (MAX (b ** k) n)` by rw[size_max] >>
    `size (MAX (b ** k) n) <= size (n * t)` by rw[size_monotone_le] >>
    decide_tac) >>
    `size (b ** k - n) <= size (n * t)` by
      (`size (b ** k - n) <= size (b ** k)` by rw[size_monotone_le] >>
    `size (b ** k) <= size (n * t)` by rw[size_monotone_le] >>
    decide_tac) >>
    `size r <= size n` by rw[size_monotone_le] >>
    `size (2 * r) <= size (2 * n)` by rw[size_monotone_le] >>
    rw[Abbr`x`] >>
    `size k + (size n + (TWICE (size r) + (TWICE (size (TWICE r)) +
      (size (b ** k - n) + (MAX (size (b ** k)) (size n) + 1))))) <=
    1 + size k + size n + 2 * size n + 2 * size (2 * n) + 2 * size (n * t)` by decide_tac >>
    `size (2 * n) = 1 + size n` by rw[size_twice] >>
    `size (n * t) <= size n + 2 * k` by rw[size_mult_two_power_upper, Abbr`t`] >>
    decide_tac
  ]) >>
  `z <= 135 * k ** 3 * size k ** 2 * size n ** 2` by
      (`z <= 15 * k ** 3 * size b ** 2 * size k ** 2` by metis_tac[expM_steps_bound] >>
  Cases_on `r = 0` >| [
    `b = 1` by rw[Abbr`b`] >>
    `15 * k ** 3 * size b ** 2 * size k ** 2 = 15 * k ** 3 * size k ** 2` by rw[] >>
    `15 * k ** 3 * size k ** 2 <= 15 * k ** 3 * size k ** 2 * size n ** 2` by rw[] >>
    decide_tac,
    `size b <= 3 * size n` by
  (`b < r * 2 ** 2` by rw[Abbr`b`] >>
    `r * 2 ** 2 <= n * 2 ** 2` by rw[] >>
    `b <= n * 2 ** 2` by decide_tac >>
    `size b <= size (n * 2 ** 2)` by rw[size_monotone_le] >>
    `size (n * 2 ** 2) <= size n + 2` by rw[size_mult_two_power_upper] >>
    `2 <= 2 * size n` by rw[] >>
    decide_tac) >>
    `15 * k ** 3 * size b ** 2 * size k ** 2 <= 15 * k ** 3 * (3 * size n) ** 2 * size k ** 2` by rw[] >>
    `15 * k ** 3 * (3 * size n) ** 2 * size k ** 2 = 15 * 9 * k ** 3 * size k ** 2 * size n ** 2` by rw[EXP_BASE_MULT] >>
    decide_tac
  ]) >>
  decide_tac);

(* A very useful result! *)

(* Theorem: let body n = (let r = ROOT k (n DIV 2 ** k) in
                if k = 0 then 0
                else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                     MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                     stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
             in !n. body n <= 155 * k ** 3 * size k ** 2 * size n ** 2 *)
(* Proof:
      body n
   <= 3 + 4 * k + size k + 7 * size n +
      5 * k * size k * size n + 135 * k ** 3 * size k ** 2 * size n ** 2  by rootM_body_upper
   <= (3 + 4 + 1 + 7 + 5 + 135) * k ** 3 * size k ** 2 * size n ** 2      by dominant term
    = 155 * k ** 3 * size k ** 2 * size n ** 2
   Can use (MAX 1 k), but body n = 0 when k = 0 in this case.
*)
val rootM_body_bound = store_thm(
  "rootM_body_bound",
  ``!k. let body n = (let r = ROOT k (n DIV 2 ** k) in
             if k = 0 then 0
             else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                  MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                  stepsOf (shrinkM n k) + stepsOf (expM (TWICE r + 1) k))
        in !n. body n <= 155 * k ** 3 * size k ** 2 * size n ** 2``,
  rpt strip_tac >>
  assume_tac rootM_body_upper >>
  last_x_assum (qspec_then `k` strip_assume_tac) >>
  qabbrev_tac `body = \n. (let r = ROOT k (n DIV 2 ** k) in if k = 0 then 0 else
            1 + size k + size n + 2 * size r + 2 * (size (2 * r)) + MAX (size ((2 * r + 1) ** k)) (size n) +
            size ((2 * r + 1) ** k - n) + stepsOf (shrinkM n k) + stepsOf (expM (2 * r + 1) k))` >>
  `!n. body n <= 155 * k ** 3 * size k ** 2 * size n ** 2` suffices_by metis_tac[] >>
  rpt strip_tac >>
  `body n <= 3 + 4 * k + size k + 7 * size n +
              5 * k * size k * size n + 135 * k ** 3 * size k ** 2 * size n ** 2` by metis_tac[] >>
  Cases_on `k = 0` >| [
    `body n = 0` by fs[Abbr`body`] >>
    decide_tac,
    qabbrev_tac `t = k ** 3 * size k ** 2 * size n ** 2` >>
    `body n <= 155 * t` suffices_by rw[Abbr`t`] >>
    `0 < t` by rw[MULT_POS, Abbr`t`] >>
    `1 <= t` by decide_tac >>
    `k <= t` by
  (`k <= k * (k ** 2 * size k ** 2 * size n ** 2)` by rw[MULT_POS] >>
    `k * (k ** 2 * size k ** 2 * size n ** 2) = t` by rw[Abbr`t`] >>
    decide_tac) >>
    `size k <= t` by
    (`size k <= size k * (k ** 3 * size k * size n ** 2)` by rw[MULT_POS] >>
    `size k * (k ** 3 * size k * size n ** 2) = t` by rw[Abbr`t`] >>
    decide_tac) >>
    `size n <= t` by
      (`size n <= size n * (k ** 3 * size k ** 2 * size n)` by rw[MULT_POS] >>
    `size n * (k ** 3 * size k ** 2 * size n) = t` by rw[Abbr`t`] >>
    decide_tac) >>
    `k * size k * size n <= t` by
        (`k * size k * size n <= k * size k * size n * (k ** 2 * size k * size n)` by rw[MULT_POS] >>
    `k * size k * size n * (k ** 2 * size k * size n) = t` by rw[Abbr`t`] >>
    decide_tac) >>
    `k ** 3 * size k ** 2 * size n ** 2 = t` by rw[Abbr`t`] >>
    decide_tac
  ]);

(* Theorem: stepsOf (rootM k n) <=
         1 + size k + 3 * size n + 4 * k * size n + size k * size n +
         7 * size n ** 2 + 5 * k * size k * size n ** 2 + 135 * k ** 3 * size k ** 2 * size n ** 3 *)
(* Proof:
   Let body = (\n. let r = ROOT k (n DIV (2 ** k)) in
               if k = 0 then 0 else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                    MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                    stepsOf (shrinkM n k) + stepsOf (expM (2 * r + 1) k)),
       cover = (\n. 3 + 4 * k + size k + 7 * size n + 5 * k * size k * size n +
                    135 * k ** 3 * size k ** 2 * size n ** 2);
       loop = stepsOf o rootM k,
          b = 2 ** k, c = 1 + size k.

   If k = 0, to show: loop n <= c + size n * cover n
      Note loop n = 1 + size n                  by rootM_steps_0_n, k = 0
       and c = 1 + size 0 = 2                   by size_0
       and 5 < cover n                          by notation, k = 0
      Hence true.

   If k <> 0, to show: loop n <= c + size n * cover n
      Note 1 < b                                by ONE_LT_EXP, 0 < k
       and !x. loop x = if x = 0 then c else body x + loop (x DIV b))
                                                by rootM_steps_by_div_loop
       and !x. body x <= cover x                by rootM_body_upper
       and MONO cover                           by size_monotone_le
      Thus loop n <= c + (pop b n) * cover n    by loop_div_count_cover_le, 1 < b
      Note pop b n <= size n                    by pop_size
           loop n
        <= 1 + sk + sn * (3 + 4 * k + sk + 7 * sn + 5 * k * sk * sn + 135 * k ** 3 * (sk * sn) ** 2))
                                                by notation
         = 1 + sk + 3 * sn + 4 * k * sn + sk * sn + 7 * sn ** 2 + 5 * k * sk * sn ** 2 + 135 * k ** 3 * sk ** 2 * sn ** 3
*)
val rootM_steps_upper = store_thm(
  "rootM_steps_upper",
  ``!k n. stepsOf (rootM k n) <=
         1 + size k + 3 * size n + 4 * k * size n + size k * size n +
         7 * size n ** 2 + 5 * k * size k * size n ** 2 + 135 * k ** 3 * size k ** 2 * size n ** 3``,
  rpt strip_tac >>
  assume_tac rootM_steps_by_div_loop >>
  first_x_assum (qspec_then `k` strip_assume_tac) >>
  assume_tac rootM_body_upper >>
  first_x_assum (qspec_then `k` strip_assume_tac) >>
  qabbrev_tac `body = \n. let r = ROOT k (n DIV (2 ** k)) in
               if k = 0 then 0
               else 1 + size k + size n + 2 * size r + 2 * size (2 * r) +
                    MAX (size ((2 * r + 1) ** k)) (size n) + size ((2 * r + 1) ** k - n) +
                    stepsOf (shrinkM n k) + stepsOf (expM (2 * r + 1) k)` >>
  qabbrev_tac `cover = \n. 3 + 4 * k + size k + 7 * size n + 5 * k * size k * size n +
                            135 * k ** 3 * size k ** 2 * size n ** 2` >>
  qabbrev_tac `loop = \n. stepsOf (rootM k n)` >>
  qabbrev_tac `b = 2 ** k` >>
  qabbrev_tac `c = 1 + size k` >>
  `c + size n * cover n = c + 3 * size n + 4 * k * size n + size k * size n + 7 * size n ** 2 +
           5 * k * size k * size n ** 2 + 135 * k ** 3 * size k ** 2 * size n ** 3` by
  (qabbrev_tac `sk = size k` >>
  qabbrev_tac `sn = size n` >>
  `sn * cover n = sn * (3 + 4 * k + sk + 7 * sn + 5 * k * sk * sn + 135 * k ** 3 * sk ** 2 * sn ** 2)` by rw[Abbr`cover`, Abbr`sk`, Abbr`sn`] >>
  `_ = 3 * sn + 4 * sn * k + sn * sk + 7 * sn * sn + 5 * sn * k * sk * sn + 135 * sn * k ** 3 * sk ** 2 * sn ** 2` by decide_tac >>
  `sn * sn = sn ** 2` by rw[] >>
  `sn * k * sk * sn = k * sk * sn ** 2` by rw[] >>
  `sn * k ** 3 * sk ** 2 * sn ** 2 = k ** 3 * sk ** 2 * sn ** 3` by rw[] >>
  decide_tac) >>
  `loop n <= c + size n * cover n` suffices_by metis_tac[] >>
  Cases_on `k = 0` >| [
    `loop n = 1 + size n` by rw[rootM_steps_0_n, Abbr`loop`] >>
    `c = 2` by rw[Abbr`c`] >>
    `size n <= size n * cover n` by rw[Abbr`cover`] >>
    decide_tac,
    `1 < b` by rw[ONE_LT_EXP, Abbr`b`] >>
    `!n. loop n = if n = 0 then c else body n + loop (n DIV b)` by metis_tac[] >>
    `!n. body n <= cover n` by metis_tac[] >>
    `MONO cover` by
  (rw[Abbr`cover`] >>
    `size x <= size y` by rw[size_monotone_le] >>
    `k * size k * size x <= k * size k * size y` by rw[] >>
    `k ** 3 * size k ** 2 * size x ** 2 <= k ** 3 * size k ** 2 * size y ** 2` by rw[] >>
    decide_tac) >>
    `loop n <= c + (pop b n) * cover n` by metis_tac[loop_div_count_cover_le] >>
    `pop b n <= size n` by rw[pop_size] >>
    `pop b n * cover n <= size n * cover n` by rw[] >>
    decide_tac
  ]);

(* Theorem: stepsOf (rootM k n) <= 157 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3 *)
(* Proof:
   Let sk = size k, sn = size n.
      stepsOf (rootM k n)
   <= 1 + sk + 3 * sn + 4 * k * sn + sk * sn + 7 * sn ** 2 +
       5 * k * sk * sn ** 2 + 135 * k ** 3 * sk ** 2 * sn ** 3        by rootM_steps_upper
   <= (1 + 1 + 3 + 4 + 1 + 7 + 5 + 135) * k ** 3 * sk ** 2 * sn ** 3  by dominant term
    = 157 * k ** 3 * sk ** 2 * sn ** 3
   Replace k by (MAX 1 k) to cater for k = 0.
*)
val rootM_steps_bound = store_thm(
  "rootM_steps_bound",
  ``!k n. stepsOf (rootM k n) <= 157 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3``,
  rpt strip_tac >>
  assume_tac rootM_steps_upper >>
  last_x_assum (qspecl_then [`k`, `n`] strip_assume_tac) >>
  qabbrev_tac `sk = size k` >>
  qabbrev_tac `sn = size n` >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m ** 3 * sk ** 2 * sn ** 3` >>
  `stepsOf (rootM k n) <= 157 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`, Abbr`sk`, Abbr`sn`] >>
  `1 <= t` by decide_tac >>
  `sk <= t` by
  (`sk <= sk * (m ** 3 * sk * sn ** 3)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sk * (m ** 3 * sk * sn ** 3) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sn <= t` by
    (`sn <= sn * (m ** 3 * sk ** 2 * sn ** 2)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sn * (m ** 3 * sk ** 2 * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * sn <= t` by
      (`k * sn <= m * sn` by rw[] >>
  `m * sn <= m * sn * (m ** 2 * sk ** 2 * sn ** 2)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `m * sn * (m ** 2 * sk ** 2 * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sk * sn <= t` by
        (`sk * sn <= sk * sn * (m ** 3 * sk * sn ** 2)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sk * sn * (m ** 3 * sk * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sn ** 2 <= t` by
          (`sn ** 2 <= sn ** 2 * (m ** 3 * sk ** 2 * sn)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sn ** 2 * (m ** 3 * sk ** 2 * sn) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * sk * sn ** 2 <= t` by
            (`k * sk * sn ** 2 <= m * sk * sn ** 2` by rw[] >>
  `m * sk * sn ** 2 <= m * sk * sn ** 2 * (m ** 2 * sk * sn)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `m * sk * sn ** 2 * (m ** 2 * sk * sn) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 3 * sk ** 2 * sn ** 3 <= t` by
              (`k ** 3 * sk ** 2 * sn ** 3 <= m ** 3 * sk ** 2 * sn ** 3` by rw[] >>
  `m ** 3 * sk ** 2 * sn ** 3 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: (stepsOf o combin$C rootM n) IN
            big_O (POLY 1 o (\k. k ** 3 * (size k) ** 2 * (size n) ** 3)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?h c. !k. h < k ==> stepsOf (rootM k n) <= c * k ** 3 * size n ** 3 * size k ** 2
   Let h = 0, c = 157.
   Then 0 < k ==> MAX 1 k = k    by MAX_DEF
   The result follows            by rootM_steps_bound
*)
val rootM_steps_O_base = store_thm(
  "rootM_steps_O_base",
  ``!n. (stepsOf o combin$C rootM n) IN
        big_O (POLY 1 o (\k. k ** 3 * (size k) ** 2 * (size n) ** 3))``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `157` >>
  rpt strip_tac >>
  assume_tac rootM_steps_bound >>
  last_x_assum (qspecl_then [`n'`, `n`] strip_assume_tac) >>
  `MAX 1 n' = n'` by rw[MAX_DEF] >>
  fs[]);

(* Theorem: (stepsOf o rootM k) IN O_poly 3 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k'. !n. h < n ==> stepsOf (rootM k n) <= k' * size n ** 3
   Note stepsOf (rootM k n) <= 157 * MAX 1 k ** 3 * size k ** 2 * size n ** 3
                                               by rootM_steps_bound
   Take any h, say 0, and k' = 157 * MAX 1 k ** 3 * size k ** 2, the result follows.
*)
val rootM_steps_O_poly = store_thm(
  "rootM_steps_O_poly",
  ``!k. (stepsOf o rootM k) IN O_poly 3``,
  rw[O_poly_thm] >>
  metis_tac[rootM_steps_bound]);

(* This is a spectacular achievement! *)

(* Theorem: (stepsOf o rootM k) IN big_O (\n. (ulog n) ** 3) *)
(* Proof:
   Note (stepsOf o rootM k) IN O_poly 3   by rootM_steps_O_poly
    and O_poly 3
      = big_O (POLY 3 o ulog)             by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 3)                 by POLY_def, FUN_EQ_THM
   The result follows.
*)
val rootM_steps_big_O = store_thm(
  "rootM_steps_big_O",
  ``!k. (stepsOf o rootM k) IN big_O (\n. (ulog n) ** 3)``,
  assume_tac rootM_steps_O_poly >>
  `O_poly 3 = big_O (POLY 3 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 3 o ulog = \n. ulog n ** 3` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (rootM k n) = ROOT k n) /\
            (stepsOf o rootM k) IN big_O (\n. (ulog n) ** 3) *)
(* Proof: by rootM_value, rootM_steps_big_O *)
val rootM_thm = store_thm(
  "rootM_thm",
  ``!k n. (valueOf (rootM k n) = ROOT k n) /\
         (stepsOf o rootM k) IN big_O (\n. (ulog n) ** 3)``,
  metis_tac[rootM_value, rootM_steps_big_O]);

(* ------------------------------------------------------------------------- *)
(* Integer Square-root in Monadic Style                                      *)
(* ------------------------------------------------------------------------- *)

(* Define integer square-root *)
val sqrtM_def = Define`
    sqrtM = rootM 2
`;

(*
> EVAL ``MAP sqrtM [0 .. 16]``;  =
      [(0,Count 3); (1,Count 45); (1,Count 49); (1,Count 49); (2,Count 123);
       (2,Count 123); (2,Count 122); (2,Count 122); (2,Count 130);
       (3,Count 130); (3,Count 130); (3,Count 130); (3,Count 130);
       (3,Count 130); (3,Count 130); (3,Count 130); (4,Count 232)]: thm
*)

(* Theorem: valueOf (sqrtM n) = SQRT n *)
(* Proof: by sqrtM_def *)
val sqrtM_value = store_thm(
  "sqrtM_value[simp]",
  ``!n. valueOf (sqrtM n) = SQRT n``,
  rw[sqrtM_def]);

(* Obtain theorems *)
val sqrtM_steps_upper = save_thm("sqrtM_steps_upper",
    rootM_steps_upper |> ISPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM sqrtM_def]);
val sqrtM_steps_bound = save_thm("sqrtM_steps_bound",
    rootM_steps_bound |> ISPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM sqrtM_def]);
val sqrtM_steps_O_poly = save_thm("sqrtM_steps_O_poly",
    rootM_steps_O_poly |> ISPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM sqrtM_def]);
val sqrtM_steps_big_O = save_thm("sqrtM_steps_big_O",
    rootM_steps_big_O |> ISPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM sqrtM_def]);
val sqrtM_thm = save_thm("sqrtM_thm",
    rootM_thm |> ISPEC ``2`` |> SIMP_RULE (bool_ss) [GSYM sqrtM_def]); (* not srw_ss() *)
(*
val sqrtM_steps_upper = |- !n. stepsOf (sqrtM n) <=
          3 + 3 * size n + 8 * size n + TWICE (size n) + 7 * size n ** 2 +
          20 * size n ** 2 + 4320 * size n ** 3: thm
val sqrtM_steps_bound = |- !n. stepsOf (sqrtM n) <= 5024 * size n ** 3: thm
val sqrtM_steps_O_poly = |- stepsOf o sqrtM IN O_poly 3: thm
val sqrtM_steps_big_O = |- stepsOf o sqrtM IN big_O (\n. ulog n ** 3): thm
val sqrtM_thm = |- !n. valueOf (sqrtM n) = SQRT n /\
                       stepsOf o sqrtM IN big_O (\n. ulog n ** 3): thm
*)

(* ------------------------------------------------------------------------- *)
(* Power Free in Monadic Style                                               *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode: compute (power_free n)
   power_free n =
      u <- ulog n                // compute loop count
      for k = 2 to u {           // (root k) starting from k = 2, k++
          if (k-th root of n) ** k = n), return False.   // not power free if a power of base
      }
      return True.               // all possible powers checked.
*)

(* Define power_free in monadic style *)
(* Note: the zeroM test is present for proof of termination.
   Generally, the caller ensures that b <> 0, and we exit when b = 1.
   But the termination logic knows nothing about the caller,
   so the zeroM test here is superfluous.
*)

(*
> power_free_upto_def;
val it = |- !n k. n power_free_upto k <=> !j. 1 < j /\ j <= k ==> ROOT j n ** j <> n: thm
*)

Definition power_free_loopM_def:
  power_free_loopM n k =
      do
        k0 <- zeroM k;
        k1 <- oneM k;
        if k0 \/ k1 then return T
        else do
               r <- rootM k n;
               m  <- expM r k;
               gd <- eqM m n;
               if gd then return F
               else do
                      k' <- decM k;
                      power_free_loopM n k';
                    od
             od
      od
Termination WF_REL_TAC `measure (λ(n,k). k)` >> simp[]
End

(*
> power_free_test_def;
val it = |- !n. power_free_test n <=> 1 < n /\ n power_free_upto ulog n: thm
*)

(* Define power_free in monadic style *)
val power_freeM_def = Define`
    power_freeM n =
      do
         m <- ulogM n;
         m0 <- zeroM m;
         if m0 then return F
         else power_free_loopM n m;
      od
`;

(*
> EVAL ``power_freeM 0``; = (F,Count 2): thm
> EVAL ``power_freeM 1``; = (F,Count 12): thm
> EVAL ``power_freeM 2``; = (T,Count 42): thm
> EVAL ``power_freeM 3``; = (T,Count 111): thm
> EVAL ``power_freeM 4``; = (F,Count 243): thm
> EVAL ``power_freeM 5``; = (T,Count 311): thm
> EVAL ``power_freeM 6``; = (T,Count 329): thm
> EVAL ``power_freeM 7``; = (T,Count 310): thm
> EVAL ``power_freeM 8``; = (F,Count 330): thm
> EVAL ``power_freeM 9``; = (F,Count 606): thm
> EVAL ``power_freeM 10``; = (T,Count 635): thm
> EVAL ``power_freeM 49``; = (F,Count 1668): thm
*)

(* Theorem: valueOf (power_free_loopM n k) = (n power_free_upto k) *)
(* Proof:
   By induction from power_free_loopM_def, to show:
   (1) n power_free_upto 0, true      by power_free_upto_0
   (2) n power_free_upto 1, true      by power_free_upto_1
   (3) k <> 0 /\ k <> 0 ==>
       valueOf (if ROOT k n ** k = n then unit F
                else do k' <- decM k; power_free_loopM n k' od) <=> n power_free_upto k
       If ROOT k n ** k = n, this is to show:
          ROOT k n ** k = n ==> ~(n power_free_upto k)
          Note 1 < k                  by k <> 0, k <> 1
            so ~(n power_free_upto k) by power_free_upto_def
       If ROOT k n ** k <> n, this to show:
          ROOT k n ** k <> n ==> n power_free_upto k - 1 <=> n power_free_upto k
          This follows                by power_free_upto_def
*)
val power_free_loopM_value = store_thm(
  "power_free_loopM_value[simp]",
  ``!n k. valueOf (power_free_loopM n k) = (n power_free_upto k)``,
  ho_match_mp_tac (theorem "power_free_loopM_ind") >>
  rw[] >>
  rw[Once power_free_loopM_def] >-
  rw[power_free_upto_0] >-
  rw[power_free_upto_1] >>
  (Cases_on `ROOT k n ** k = n` >> simp[]) >| [
    spose_not_then strip_assume_tac >>
    `1 < k` by decide_tac >>
    fs[power_free_upto_def],
    rw[power_free_upto_def, EQ_IMP_THM] >>
    metis_tac[LESS_OR_EQ, DECIDE``j < k ==> j <= k - 1``]
  ]);

(* Theorem: valueOf (power_freeM n) = power_free_test n *)
(* Proof:
   By power_freeM_def, this is to show:
   (1) ulog n = 0 ==>
       Note n = 0 or n = 1           by ulog_eq_0
       Thus ~power_free_test n       by power_free_test_def
   (2) ulog n <> 0 ==> power_free_upto n (ulog n) <=> power_free_test n
       Note n <> 0 /\ n <> 1         by ulog_eq_0
         so 1 < n                    by n <> 0, n <> 1
       The result follows            by power_free_test_def, 1 < n
*)
val power_freeM_value = store_thm(
  "power_freeM_value[simp]",
  ``!n. valueOf (power_freeM n) = power_free_test n``,
  rw[power_freeM_def, power_free_test_def, ulog_eq_0]);

(* Theorem: valueOf (power_freeM n) = power_free n *)
(* Proof: by power_freeM_value, power_free_test_eqn. *)
val power_freeM_value_alt = store_thm(
  "power_freeM_value_alt",
  ``!n. valueOf (power_freeM n) = power_free n``,
  rw[power_free_test_eqn]);

(* Theorem: stepsOf (power_freeM n) =
            if n = 0 then 2
            else if n = 1 then 12
                 else stepsOf (ulogM n) + size (ulog n) + stepsOf (power_free_loopM n (ulog n)) *)
(* Proof:
     stepsOf (power_freeM n)
   = stepsOf (ulogM n) + stepsOf (zeroM (ulog n)) +
     if (ulog n = 0) then 0 else stepsOf (power_free_loopM n (ulog n))
   = stepsOf (ulogM n) + size (ulog n) +
     if n <= 1 then 0 else stepsOf (power_free_loopM n (ulog n))
   = if n = 0 then stepsOf (ulogM 0) + size (ulog 0)
     else n = 1 then stepsOf (ulogM 1) + size (ulog 1)
     else stepsOf (ulogM n) + size (ulog n) + stepsOf (power_free_loopM n (ulog n))
   = if n = 0 then 1 + 1                 by ulog_0, ulogM_steps_0, size_0
     else if n = 1 then 11 + 1           by ulog_1, ulogM_steps_1, size_0
     else stepsOf (ulogM n) + size (ulog n) + stepsOf (power_free_loopM n (ulog n))
   = if n = 0 then 2 else if n = 1 then 12
     else stepsOf (ulogM n) + size (ulog n) + stepsOf (power_free_loopM n (ulog n))
*)
val power_freeM_steps_thm = store_thm(
  "power_freeM_steps_thm",
  ``!n. stepsOf (power_freeM n) =
        if n = 0 then 2
        else if n = 1 then 12
             else stepsOf (ulogM n) + size (ulog n) + stepsOf (power_free_loopM n (ulog n))``,
  rpt strip_tac >>
  `(ulog 0 = 0) /\ (ulog 1 = 0)` by rw[] >>
  (rw[power_freeM_def] >> simp[]) >-
  rw[ulogM_steps_0] >-
  rw[ulogM_steps_1] >>
  fs[ulog_eq_0]);

(* Theorem: stepsOf (power_free_loopM n 0) = 2 *)
(* Proof:
     stepsOf (power_free_loopM n 0)
   = stepsOf (zeroM 0) + stepsOf (oneM 0)   by power_free_loopM_def
   = size 0 + size 0 = 1 + 1 = 2            by size_0
*)
val power_free_loopM_steps_n_0 = store_thm(
  "power_free_loopM_steps_n_0",
  ``!n. stepsOf (power_free_loopM n 0) = 2``,
  rw[Once power_free_loopM_def]);

(* Theorem: stepsOf (power_free_loopM n k) =
            2 * size k +
            if k = 0 \/ k = 1 then 0
            else size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                 if ((ROOT k n) ** k = n) then 0
                 else size k + stepsOf (power_free_loopM n (k - 1)) *)
(* Proof:
     stepsOf (power_free_loopM n k)
   = stepsOf (zeroM k) +
     stepsOf (oneM k) +
     if (k = 0) \/ (k = 1) then 0
     else stepsOf (rootM k n) +
          stepsOf (expM (ROOT k n) k) +
          stepsOf (eqM ((ROOT k n) ** k) n) +
          if ((ROOT k n) ** k = n) the 0
          else stepsOf (decM k) +
               stepsOf (power_free_loopM n (k - 1))    by power_free_loopM_def
   = size k + size k + if k = 0 \/ k = 1 then 0
     else stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
          MAX (size ((ROOT k n) ** k)) (size n) + if ((ROOT k n) ** k = n) then 0
          else size k + stepsOf (power_free_loopM n (k - 1))
     Let m = (ROOT k n) ** k.
     Then m <= n         by ROOT, 0 < k.
       so MAX (size m) (size n) = size (MAX m n) = size n    by size_max, MAX_DEF

   = 2 * size k + if k = 0 \/ k = 1 then 0
     else stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
          size n + if ((ROOT k n) ** k = n) then 0
          else size k + stepsOf (power_free_loopM n (k - 1))
*)
val power_free_loopM_steps_thm = store_thm(
  "power_free_loopM_steps_thm",
  ``!n k. stepsOf (power_free_loopM n k) =
          2 * size k +
          if k = 0 \/ k = 1 then 0
          else size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
               if ((ROOT k n) ** k = n) then 0
               else size k + stepsOf (power_free_loopM n (k - 1))``,
  rpt strip_tac >>
  `0 < k ==> MAX (size (ROOT k n ** k)) (size n) = size n` by
  (rpt strip_tac >>
  qabbrev_tac `r = (ROOT k n) ** k` >>
  `r <= n` by rw[ROOT, Abbr`r`] >>
  `MAX r n = n` by rw[MAX_DEF] >>
  rw[GSYM size_max]) >>
  (rw[] >> rw[Once power_free_loopM_def]));

(* Theorem: let eq k = ((ROOT k n) ** k = n);
                body k =
                  if k <= 1 then 2
                  else size n + 2 * size k +
                       stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
             in !k. stepsOf (power_free_loopM n k) =
                    if k = 0 then 2
                    else body k + if eq k then 0 else stepsOf (power_free_loopM n (k - 1)) *)
(* Proof:
     stepsOf (power_free_loopM n k)
   = 2 * size k + if k = 0 \/ k = 1 then 0
     else stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
          size n + if ((ROOT k n) ** k = n) then 0
          else size k + stepsOf (power_free_loopM n (k - 1))    by power_free_loopM_steps_thm
   = if k = 0 \/ k = 1 then 2
     else (2 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
          size n + if (ROOT k n) ** k = n then 0 else size k) +
          if (ROOT k n) ** k = n then 0 else stepsOf (power_free_loopM n (k - 1))
   = if k = 0 then 2
     else if k = 1 then 2
     else (2 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
          size n + if (ROOT k n) ** k = n then 0 else size k) +
          if (ROOT k n) ** k = n then 0 else stepsOf (power_free_loopM n (k - 1))
*)
val power_free_loopM_steps_by_dec_loop = store_thm(
  "power_free_loopM_steps_by_dec_loop",
  ``!n. let eq k = ((ROOT k n) ** k = n);
           body k =
              if k <= 1 then 2
              else size n + 2 * size k +
                   stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
        in !k. stepsOf (power_free_loopM n k) =
               if k = 0 then 2
               else body k + if eq k then 0 else stepsOf (power_free_loopM n (k - 1))``,
  (rw[Once power_free_loopM_steps_thm] >> rw[]) >-
  rw[] >>
  fs[ROOT_1]);

(*
This puts power_free_loopM_steps in the category: decreasing loop with body cover and exit.
   sizeM_steps_by_div_loop:
        !k. loop k = if k = 0 then 2 else body k + if eq k then 0 else loop (k - 1)
suitable for: loop_dec_count_cover_exit_le
*)

(* Work out a cover for the body *)

(* Theorem: let eq k = ((ROOT k n) ** k = n);
                body k =
                    if k <= 1 then 2
                    else size n + 2 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                         if eq k then 0 else size k
             in !k. body k <=
                    size n + 3 * size k + 15 * k ** 3 * size k ** 2 * size n ** 2 + 157 * k ** 3 * size k ** 2 * size n ** 3 *)
(* Proof:
   If k <= 1,
      body k = 2, so this is trivial as 1 <= size k    by one_le_size
   If 1 < k,
      body k
    = if k <= 1 then 2
      else 2 * size k + size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
           if eq k then 0 else size k
   <= size n + 2 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + size k
    = size n + 3 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k)

   Let x = size n + 3 * size k,
       y = stepsOf (rootM k n),
       z = stepsOf (expM (ROOT k n) k)
   Then y <= 157 * (MAX 1 k) ** 3 * size k ** 2 * size n ** 3  by rootM_steps_bound
    and z <= 15 * (MAX 1 k) ** 3 * size b ** 2 * size k ** 2   by expM_steps_bound, b = ROOT k n.
    but b = ROOT k n <= n                              by ROOT_LE_SELF, 0 < k
     so size b = size (ROOT k n) <= size n             by size_monotone_le
   Note MAX 1 k = k                                    by 0 < k.
   Thus x + y + z
     <= size n + 3 * size k + 157 * k ** 3 * size k ** 2 * size n ** 3 + 15 * k ** 3 * size k ** 2 * size n ** 2
*)
val power_free_loopM_body_upper = store_thm(
  "power_free_loopM_body_upper",
  ``!n. let eq k = ((ROOT k n) ** k = n);
           body k =
             if k <= 1 then 2
             else size n + 2 * size k + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                  if eq k then 0 else size k
        in !k. body k <=
               size n + 3 * size k + 15 * k ** 3 * size k ** 2 * size n ** 2 + 157 * k ** 3 * size k ** 2 * size n ** 3``,
  rw_tac std_ss[] >>
  Cases_on `k <= 1` >| [
    `body k = 2` by metis_tac[] >>
    `0 < size k` by rw[] >>
    decide_tac,
    `0 < k /\ 1 < k` by decide_tac >>
    `MAX 1 k = k` by rw[MAX_DEF] >>
    qabbrev_tac `sk = size k` >>
    qabbrev_tac `sn = size n` >>
    `body k <= sn + 3 * sk + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k)` by rw[Abbr`body`, Abbr`eq`, Abbr`sk`, Abbr`sn`] >>
    qabbrev_tac `y = stepsOf (rootM k n)` >>
    qabbrev_tac `z = stepsOf (expM (ROOT k n) k)` >>
    `y <= 157 * k ** 3 * sk ** 2 * sn ** 3` by metis_tac[rootM_steps_bound] >>
    `z <= 15 * k ** 3 * sk ** 2 * sn ** 2` by
  (`z <= 15 * k ** 3 * size (ROOT k n) ** 2 * sk ** 2` by metis_tac[expM_steps_bound] >>
    `ROOT k n <= n` by rw[ROOT_LE_SELF] >>
    `size (ROOT k n) <= sn` by rw[size_monotone_le, Abbr`sn`] >>
    `k ** 3 * size (ROOT k n) ** 2 * sk ** 2 <= k ** 3 * sn ** 2 * sk ** 2` by rw[] >>
    decide_tac) >>
    decide_tac
  ]);

(* Theorem: let eq k = ((ROOT k n) ** k = n);
                body k =
                  if k <= 1 then 2
                  else size n + 2 * size k +
                       stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
             in !k. body k <= 176 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3 *)
(* Proof:
      body k
   <= size n + 3 * size k + 15 * k ** 3 * size k ** 2 * size n ** 2 +
          157 * k ** 3 * size k ** 2 * size n ** 3                 by power_free_loopM_body_upper
   <= (1 + 3 + 15 + 157) * k ** 3 * (size k) ** 2 * (size n) ** 3  by dominant term
    = 176 * k ** 3 * (size k) ** 2 * (size n) ** 3
   Use (MAX 1 k) to cater for k = 0.
*)
val power_free_loopM_body_bound = store_thm(
  "power_free_loopM_body_bound",
  ``!n. let eq k = ((ROOT k n) ** k = n);
           body k =
             if k <= 1 then 2
             else size n + 2 * size k +
                  stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k
        in !k. body k <= 176 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3``,
  rpt strip_tac >>
  assume_tac power_free_loopM_body_upper >>
  last_x_assum (qspecl_then [`n`] strip_assume_tac) >>
  qabbrev_tac `eq = \k. ROOT k n ** k = n` >>
  qabbrev_tac `body = \k. if k <= 1 then 2
    else 2 * size k + size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) + if eq k then 0 else size k` >>
  `!k. body k <= 176 * (MAX 1 k) ** 3 * size k ** 2 * size n ** 3` suffices_by rw[Abbr`body`, Abbr`eq`] >>
  rpt strip_tac >>
  `body k <= size n + 3 * size k + 15 * k ** 3 * size k ** 2 * size n ** 2 + 157 * k ** 3 * size k ** 2 * size n ** 3` by fs[Abbr`body`, Abbr`eq`] >>
  qabbrev_tac `sn = size n` >>
  qabbrev_tac `sk = size k` >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m ** 3 * sk ** 2 * sn ** 3` >>
  `body k <= 176 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`, Abbr`sn`, Abbr`sk`] >>
  `sn <= t` by
  (`sn <= sn * (m ** 3 * sk ** 2 * sn ** 2)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sn * (m ** 3 * sk ** 2 * sn ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sk <= t` by
    (`sk <= sk * (m ** 3 * sk * sn ** 3)` by rw[MULT_POS, Abbr`sk`, Abbr`sn`] >>
  `sk * (m ** 3 * sk * sn ** 3) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 3 * sk ** 2 * sn ** 2 <= t` by
      (`k ** 3 * sk ** 2 * sn ** 2 <= m ** 3 * sk ** 2 * sn ** 2` by rw[] >>
  `m ** 3 * sk ** 2 * sn ** 2 <= m ** 3 * sk ** 2 * sn ** 2 * sn` by rw[MULT_POS, Abbr`sn`] >>
  `m ** 3 * sk ** 2 * sn ** 2 * sn = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 3 * sk ** 2 * sn ** 3 <= t` by rw[Abbr`t`] >>
  decide_tac);

(* Theorem: stepsOf (power_free_loopM n k) <= 2 + 176 * k ** 4 * size k ** 2 * size n ** 3 *)
(* Proof:
   Let eq = (\k. ROOT k n ** k = n),
       body = (\k. if k <= 1 then 2
                   else 2 * size k + size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                        if eq k then 0 else size k),
       cover = (\k. 176 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3),
       loop = (\k. stepsOf (power_free_loopM n k)).
   Then !k. loop k = if k = 0 then 2 else body k + if eq k then 0 else loop (k - 1)
                                       by power_free_loopM_steps_by_dec_loop
   If k = 0,
      loop k = 2, so this is trivial.
   If k <> 0,
      Then MAX 1 k = k                 by MAX_DEF
    Now !x. body x <= cover x          by power_free_loopM_body_bound
    and MONO cover                     by size_monotone_le
   Thus loop k
     <= 2 + hop 1 k * cover k          by loop_dec_count_cover_exit_le
      = 2 + k * cover k                by hop_1_n
     <= 2 + k * (176 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3)
                                       by notation
      = 2 + k * (176 * k ** 3 * (size k) ** 2 * (size n) ** 3)
                                       by MAX 1 k = k
      = 2 + 176 * k ** 4 * size k ** 2 * size n ** 3
                                       by EXP
*)
val power_free_loopM_steps_upper = store_thm(
  "power_free_loopM_steps_upper",
  ``!n k. stepsOf (power_free_loopM n k) <= 2 + 176 * k ** 4 * size k ** 2 * size n ** 3``,
  rpt strip_tac >>
  assume_tac power_free_loopM_steps_by_dec_loop >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  assume_tac power_free_loopM_body_bound >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `eq = \k. ROOT k n ** k = n` >>
  qabbrev_tac `body = \k. if k <= 1 then 2
                else 2 * size k + size n + stepsOf (rootM k n) + stepsOf (expM (ROOT k n) k) +
                         if eq k then 0 else size k` >>
  qabbrev_tac `cover = \k. 176 * (MAX 1 k) ** 3 * (size k) ** 2 * (size n) ** 3` >>
  qabbrev_tac `loop = \k. stepsOf (power_free_loopM n k)` >>
  Cases_on `k = 0` >| [
    `stepsOf (power_free_loopM n k) = 2` by metis_tac[] >>
    decide_tac,
    `MAX 1 k = k` by rw[MAX_DEF] >>
    `loop k <= 2 + k * (cover k)` suffices_by rw[Abbr`loop`, Abbr`cover`] >>
    `0 < 1` by decide_tac >>
    `!x. body x <= cover x` by fs[] >>
    `MONO cover` by rw[size_monotone_le, LE_MONO_MULT2, Abbr`cover`] >>
    `!k. loop k = if k = 0 then 2 else body k + if eq k then 0 else loop (k - 1)` by fs[] >>
    imp_res_tac loop_dec_count_cover_exit_le >>
    first_x_assum (qspec_then `k` strip_assume_tac) >>
    metis_tac[hop_1_n]
  ]);

(* Theorem: stepsOf (power_free_loopM n k) <= 178 * (MAX 1 k) ** 4 * size k ** 2 * size n ** 3 *)
(* Proof:
      stepsOf (power_free_loopM n k)
   <= 2 + 176 * k ** 4 * size k ** 2 * size n ** 3      by power_free_loopM_steps_upper
   <= (2 + 176) * k ** 4 * size k ** 2 * size n ** 3    by dominant term
    = 178 * k ** 4 * size k ** 2 * size n ** 3
   Use (MAX 1 k) to take care of k = 0.
*)
val power_free_loopM_steps_bound = store_thm(
  "power_free_loopM_steps_bound",
  ``!n k. stepsOf (power_free_loopM n k) <= 178 * (MAX 1 k) ** 4 * size k ** 2 * size n ** 3``,
  rpt strip_tac >>
  assume_tac power_free_loopM_steps_upper >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  qabbrev_tac `m = MAX 1 k` >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `2 <= 2 * m ** 4 * size k ** 2 * size n ** 3` by rw[MULT_POS] >>
  `k ** 4 * size k ** 2 * size n ** 3 <= m ** 4 * size k ** 2 * size n ** 3` by rw[] >>
  decide_tac);

(* Theorem: (stepsOf o power_free_loopM n) IN
            big_O (POLY 1 o (\k. k ** 4 * (size k) ** 2 * (size n) ** 3)) *)
(* Proof:
   By big_O_def, POLY_def, this is to show:
      ?k c. !x. k < x ==> stepsOf (power_free_loopM n x) <=
                          c * (x ** 4 * size x ** 2 * size n ** 3)
   Note !k. stepsOf (power_free_loopM n k) <=
            178 * (MAX 1 k) ** 4 * size k ** 2 * size n ** 3  by power_free_loopM_steps_bound
   Let k = 0, c = 178, the result follows.
*)
val power_free_loopM_steps_O_base = store_thm(
  "power_free_loopM_steps_O_base",
  ``!n. (stepsOf o power_free_loopM n) IN
            big_O (POLY 1 o (\k. k ** 4 * (size k) ** 2 * (size n) ** 3))``,
  rw_tac bool_ss[big_O_def, POLY_def, GSPECIFICATION, combinTheory.o_THM, EXP_1] >>
  qexists_tac `0` >>
  qexists_tac `178` >>
  rpt strip_tac >>
  `MAX 1 n' = n'` by rw[MAX_DEF] >>
  metis_tac[power_free_loopM_steps_bound, MULT_ASSOC]);

(* Theorem: stepsOf (power_freeM n) <= 11 + 9 * size n + 11 * size n ** 2 + 176 * size n ** 9 *)
(* Proof:
     stepsOf (power_freeM n)
   = if n = 0 then 2 else if n = 1 then 12
     else stepsOf (ulogM n) + size (ulog n) +
          stepsOf (power_free_loopM n (ulog n))                  by power_freeM_steps_thm
   Let k = ulog n,
   Note k <= size n               by size_ulog
    and k <= n                    by ulog_le_self
   Thus size k <= size n          by size_monotone_le
   Note stepsOf (ulogM n) <= 9 + 8 * size n + 11 * size n ** 2   by ulogM_steps_upper
    and stepsOf (power_free_loopM n k)
      <= 2 + 176 * k ** 4 * size k ** 2 * size n ** 3            by power_free_loopM_steps_upper
      <= 2 + 176 * (size n) ** 4 * size n ** 2 * sizne n ** 3
       = 2 + 176 * (size n) ** 9
   Thus stepsOf (power_freeM n)
     <= 9 + 8 * size n + 11 * size n ** 2 + size n + 2 + 176 * size n ** 9    by above
      = 11 + 9 * size n + 11 * size n ** 2 + 176 * size n ** 9
*)
val power_freeM_steps_upper = store_thm(
  "power_freeM_steps_upper",
  ``!n. stepsOf (power_freeM n) <= 11 + 9 * size n + 11 * size n ** 2 + 176 * size n ** 9``,
  rpt strip_tac >>
  assume_tac power_freeM_steps_thm >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  (Cases_on `n = 0` >> simp[]) >>
  (Cases_on `n = 1` >> simp[]) >>
  qabbrev_tac `k = ulog n` >>
  qabbrev_tac `sn = size n` >>
  `k <= n` by rw[ulog_le_self, Abbr`k`] >>
  `size k <= sn` by rw[size_monotone_le, Abbr`sn`] >>
  `stepsOf (ulogM n) <= 9 + 8 * sn + 11 * sn ** 2` by rw[ulogM_steps_upper, Abbr`sn`] >>
  `stepsOf (power_free_loopM n k) <= 2 + 176 * sn ** 9` by
  (`stepsOf (power_free_loopM n k) <= 2 + 176 * k ** 4 * size k ** 2 * sn ** 3` by rw[power_free_loopM_steps_upper, Abbr`sn`] >>
  `k <= sn` by rw[size_ulog, Abbr`k`, Abbr`sn`] >>
  `k ** 4 * size k ** 2 * sn ** 3 <= sn ** 4 * size k ** 2 * sn ** 3` by rw[] >>
  `sn ** 4 * size k ** 2 * sn ** 3 <= sn ** 4 * sn ** 2 * sn ** 3` by rw[] >>
  `sn ** 4 * sn ** 2 * sn ** 3 = sn ** 9` by rw[EXP_BASE_MULT] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf (power_freeM n) <= 207 * size n ** 9 *)
(* Proof:
      stepsOf (power_freeM n)
   <= 11 + 9 * size n + 11 * size n ** 2 + 176 * size n ** 9   by power_freeM_steps_upper
   <= (11 + 9 + 11 + 176) * size n ** 9                        by dominant term
    = 207 * size n ** 9
*)
val power_freeM_steps_bound = store_thm(
  "power_freeM_steps_bound",
  ``!n. stepsOf (power_freeM n) <= 207 * size n ** 9``,
  rpt strip_tac >>
  assume_tac power_freeM_steps_upper >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `z = size n` >>
  `0 < z` by rw[Abbr`z`] >>
  `0 < z ** 9` by rw[] >>
  `z <= z * z ** 8` by rw[] >>
  `z ** 2 <= z ** 2 * z ** 7` by rw[] >>
  `z * z ** 8 = z ** 9` by rw[] >>
  `z ** 2 * z ** 7 = z ** 9` by rw[] >>
  decide_tac);

(* Theorem: (stepsOf o power_freeM) IN O_poly 9 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (power_freeM n) <= k * size n ** 9
   Note stepsOf (power_freeM n) <= 207 * size n ** 9   by power_freeM_steps_bound
   Take any h, say 0, and k = 207, the result follows.
*)
val power_freeM_steps_O_poly = store_thm(
  "power_freeM_steps_O_poly",
  ``(stepsOf o power_freeM) IN O_poly 9``,
  rw[O_poly_thm] >>
  metis_tac[power_freeM_steps_bound]);

(* This is the first truly significant complexity result! *)

(* Theorem: (stepsOf o power_freeM) IN big_O (\n. (ulog n) ** 9) *)
(* Proof:
   Note (stepsOf o power_freeM) IN O_poly 9     by power_freeM_steps_O_poly
    and O_poly 9
      = big_O (POLY 9 o ulog)                   by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 9)                       by POLY_def, FUN_EQ_THM
   The result follows.
*)
val power_freeM_steps_big_O = store_thm(
  "power_freeM_steps_big_O",
  ``(stepsOf o power_freeM) IN big_O (\n. (ulog n) ** 9)``,
  assume_tac power_freeM_steps_O_poly >>
  `O_poly 9 = big_O (POLY 9 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 9 o ulog = \n. ulog n ** 9` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (power_freeM n) <=> power_free n) /\
            (stepsOf o power_freeM) IN big_O (\n. (ulog n) ** 9) *)
(* Proof: by power_freeM_value_alt, power_freeM_steps_big_O *)
val power_freeM_thm = store_thm(
  "power_freeM_thm",
  ``!n. (valueOf (power_freeM n) <=> power_free n) /\
       (stepsOf o power_freeM) IN big_O (\n. (ulog n) ** 9)``,
  metis_tac[power_freeM_value_alt, power_freeM_steps_big_O]);

(*
From the AKS paper, the best-known power-free test is in O((log n) ** 3).
Reference:
Joachim von zur Gathen and Jürgen Gerhard. Modern Computer Algebra (1999)
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
